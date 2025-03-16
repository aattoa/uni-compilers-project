use crate::ir::{self, InstrKind};
use crate::{ast, db};

struct Binding {
    name: db::Name,
    var_id: ir::VarId,
    used: bool,
}

struct Solution {
    lhs: ir::TypeId,
    rhs: ir::TypeId,
}

#[derive(Default)]
struct ScopeLayer {
    bindings: Vec<Binding>,
    diverged: bool,
}

#[derive(Default)]
struct Scope {
    stack: Vec<ScopeLayer>,
}

struct Context {
    arena: ir::Arena,
    constants: ir::Constants,
    diagnostics: Vec<db::Diagnostic>,
    current_label: usize,
}

impl ScopeLayer {
    fn bind(&mut self, name: db::Name, var_id: ir::VarId) {
        self.bindings.push(Binding { name, var_id, used: false });
    }
}

impl Scope {
    fn top(&mut self) -> &mut ScopeLayer {
        self.stack.last_mut().unwrap()
    }
    fn bottom(&mut self) -> &mut ScopeLayer {
        self.stack.first_mut().unwrap()
    }
}

impl Context {
    fn new() -> Self {
        let mut arena = ir::Arena::default();
        let constants = ir::Constants::new(&mut arena);
        Self { arena, constants, diagnostics: Vec::new(), current_label: 0 }
    }
    fn label(&mut self) -> ir::Label {
        let index = self.current_label;
        self.current_label += 1;
        ir::Label { index }
    }
    fn var(&mut self, ir: &mut ir::Function, typ: ir::TypeId) -> ir::VarId {
        ir.locals += 1;
        self.arena.var.push(ir::Variable::local(typ, ir.locals as isize * -8))
    }
}

fn type_eq(
    arena: &ir::Arena,
    solutions: &mut Vec<Solution>,
    lhs: ir::TypeId,
    rhs: ir::TypeId,
) -> bool {
    match (&arena.typ[lhs], &arena.typ[rhs]) {
        (ir::Type::Integer, ir::Type::Integer) => true,
        (ir::Type::Boolean, ir::Type::Boolean) => true,
        (ir::Type::Unit, ir::Type::Unit) => true,
        (ir::Type::Never, ir::Type::Never) => true,
        (ir::Type::Never, _) => {
            solutions.push(Solution { lhs, rhs });
            true
        }
        (_, ir::Type::Never) => {
            solutions.push(Solution { lhs: rhs, rhs: lhs });
            true
        }
        (
            ir::Type::Function { params: lparams, ret: lret },
            ir::Type::Function { params: rparams, ret: rret },
        ) => {
            lparams.len() == rparams.len()
                && type_eq(arena, solutions, *lret, *rret)
                && std::iter::zip(lparams.iter(), rparams.iter())
                    .all(|(&lhs, &rhs)| type_eq(arena, solutions, lhs, rhs))
        }
        _ => false,
    }
}

fn expect_type_eq(
    ctx: &mut Context,
    range: db::Range,
    expected: ir::TypeId,
    found: ir::TypeId,
) -> db::Result<()> {
    let mut solutions = Vec::new();
    if type_eq(&ctx.arena, &mut solutions, expected, found) {
        for Solution { lhs, rhs } in solutions {
            ctx.arena.typ[lhs] = ctx.arena.typ[rhs].clone();
        }
        return Ok(());
    }
    let message = format!(
        "Expected {}, but found {}",
        expected.display(&ctx.arena),
        found.display(&ctx.arena)
    );
    Err(db::Diagnostic::error(range, message))
}

fn expect_unit(ctx: &mut Context, range: db::Range, variable: ir::VarId) -> db::Result<()> {
    expect_type_eq(ctx, range, ctx.constants.unit_type, ctx.arena.var[variable].typ)
}

fn expect_boolean(ctx: &mut Context, range: db::Range, variable: ir::VarId) -> db::Result<()> {
    expect_type_eq(ctx, range, ctx.constants.boolean_type, ctx.arena.var[variable].typ)
}

fn expect_integer(ctx: &mut Context, range: db::Range, variable: ir::VarId) -> db::Result<()> {
    expect_type_eq(ctx, range, ctx.constants.integer_type, ctx.arena.var[variable].typ)
}

fn lookup_variable(scope: &mut Scope, name: &db::Name) -> db::Result<ir::VarId> {
    for layer in scope.stack.iter_mut().rev() {
        for binding in layer.bindings.iter_mut().rev() {
            if binding.name.string == name.string {
                binding.used = true;
                return Ok(binding.var_id);
            }
        }
    }
    Err(db::Diagnostic::error(name.range, format!("Undeclared identifier: {}", name.string)))
}

fn unused_variable_warnings(layer: &ScopeLayer) -> impl Iterator<Item = db::Diagnostic> + '_ {
    layer.bindings.iter().filter(|binding| !binding.used).map(|Binding { name, .. }| {
        db::Diagnostic::warning(name.range, format!("Unused variable: {}", name.string))
    })
}

fn fresh_never_var(ctx: &mut Context) -> ir::VarId {
    let typ = ctx.arena.typ.push(ir::Type::Never);
    ctx.arena.var.push(ir::Variable::builtin(typ, ir::Builtin::Never))
}

fn diverge(ctx: &mut Context, scope: &mut Scope) -> ir::VarId {
    scope.top().diverged = true;
    fresh_never_var(ctx)
}

fn write(ir: &mut ir::Function, range: db::Range, kind: InstrKind) -> usize {
    ir.instructions.push(ir::Instruction { kind, range });
    ir.instructions.len() - 1
}

fn patch(ir: &mut ir::Function, offset: usize, kind: InstrKind) {
    debug_assert!(matches!(ir.instructions[offset].kind, ir::InstrKind::Placeholder));
    ir.instructions[offset].kind = kind;
}

#[derive(Default)]
struct LoopInfo {
    break_offsets: Vec<usize>,
    continue_offsets: Vec<usize>,
}

fn with_scope<T>(
    scope: &mut Scope,
    callback: impl FnOnce(&mut Scope) -> db::Result<T>,
) -> db::Result<(T, ScopeLayer)> {
    scope.stack.push(ScopeLayer::default());
    let result = callback(scope)?;
    let layer = scope.stack.pop().unwrap();
    Ok((result, layer))
}

fn discard(ctx: &mut Context, var: ir::VarId, range: db::Range) {
    if !ctx.arena.typ[ctx.arena.var[var].typ].is_zero_sized() {
        ctx.diagnostics.push(db::Diagnostic::warning(
            range,
            format!("Discarded expression of type {}", ctx.arena.var[var].typ.display(&ctx.arena)),
        ));
    }
}

fn check_expr(
    ctx: &mut Context,
    scope: &mut Scope,
    ir: &mut ir::Function,
    ast: &ast::Arena,
    loop_info: &mut Option<LoopInfo>,
    expr: ast::ExprId,
) -> db::Result<ir::VarId> {
    let range = ast.expr[expr].range;
    if scope.top().diverged {
        let message = "This expression is unreachable, because the branch has diverged";
        return Err(db::Diagnostic::error(range, message));
    }
    match &ast.expr[expr].kind {
        &ast::ExprKind::Parenthesized { inner } => {
            check_expr(ctx, scope, ir, ast, loop_info, inner)
        }
        &ast::ExprKind::Integer { literal } => {
            let dst_var = ctx.var(ir, ctx.constants.integer_type);
            write(ir, range, InstrKind::Constant { value: literal, dst_var });
            Ok(dst_var)
        }
        &ast::ExprKind::Boolean { literal } => {
            let dst_var = ctx.var(ir, ctx.constants.boolean_type);
            write(ir, range, InstrKind::Constant { value: literal as i64, dst_var });
            Ok(dst_var)
        }
        ast::ExprKind::Variable { name } => {
            let src_var = lookup_variable(scope, name)?;
            let dst_var = ctx.var(ir, ctx.arena.var[src_var].typ);
            write(ir, range, InstrKind::Copy { src_var, dst_var });
            Ok(dst_var)
        }
        ast::ExprKind::Declaration { name, typ, initializer } => {
            let init = check_expr(ctx, scope, ir, ast, loop_info, *initializer)?;
            if let &Some(typ) = typ {
                let range = ast.expr[*initializer].range;
                let expected = check_type(ctx, ast, typ)?;
                expect_type_eq(ctx, range, expected, ctx.arena.var[init].typ)?;
            }
            scope.top().bind(name.clone(), init);
            Ok(ctx.constants.unit_var)
        }
        ast::ExprKind::Block { effects, result } => {
            let (result, layer) = with_scope(scope, |scope| {
                for &effect in effects {
                    let dst = check_expr(ctx, scope, ir, ast, loop_info, effect)?;
                    discard(ctx, dst, ast.expr[effect].range);
                }
                if let &Some(result) = result {
                    check_expr(ctx, scope, ir, ast, loop_info, result)
                }
                else {
                    Ok(ctx.constants.unit_var)
                }
            })?;
            ctx.diagnostics.extend(unused_variable_warnings(&layer));
            if layer.diverged { Ok(fresh_never_var(ctx)) } else { Ok(result) }
        }
        &ast::ExprKind::Return { result } => {
            if let Some(result) = result {
                let var = check_expr(ctx, scope, ir, ast, loop_info, result)?;
                expect_type_eq(
                    ctx,
                    ast.expr[result].range,
                    ir.return_type,
                    ctx.arena.var[var].typ,
                )?;
                write(ir, range, InstrKind::Return { var });
            }
            else if matches!(ctx.arena.typ[ir.return_type], ir::Type::Unit) {
                write(ir, range, InstrKind::Return { var: ctx.constants.unit_var });
            }
            else {
                return Err(db::Diagnostic::error(range, "Missing return value"));
            }
            Ok(diverge(ctx, scope))
        }
        &ast::ExprKind::Conditional { condition, true_branch, false_branch } => {
            let condition_var = check_expr(ctx, scope, ir, ast, loop_info, condition)?;
            expect_boolean(ctx, ast.expr[condition].range, condition_var)?;

            let (then_label, else_label, exit_label) = (ctx.label(), ctx.label(), ctx.label());
            write(ir, range, InstrKind::ConditionalJump { condition_var, then_label, else_label });
            write(ir, range, InstrKind::Label { label: then_label });

            let (true_branch_var, layer) =
                with_scope(scope, |scope| check_expr(ctx, scope, ir, ast, loop_info, true_branch))?;
            ctx.diagnostics.extend(unused_variable_warnings(&layer));

            if let Some(false_branch) = false_branch {
                let copy_placeholder = write(ir, range, InstrKind::Placeholder);
                write(ir, range, InstrKind::Jump { target_label: exit_label });
                write(ir, range, InstrKind::Label { label: else_label });

                let (false_branch_var, _layer) = with_scope(scope, |scope| {
                    check_expr(ctx, scope, ir, ast, loop_info, false_branch)
                })?;
                ctx.diagnostics.extend(unused_variable_warnings(&layer));

                expect_type_eq(
                    ctx,
                    range,
                    ctx.arena.var[true_branch_var].typ,
                    ctx.arena.var[false_branch_var].typ,
                )?;

                let dst_var = ctx.var(ir, ctx.arena.var[true_branch_var].typ);
                patch(ir, copy_placeholder, InstrKind::Copy { src_var: true_branch_var, dst_var });
                write(ir, range, InstrKind::Copy { src_var: false_branch_var, dst_var });
                write(ir, range, InstrKind::Label { label: exit_label });
                Ok(dst_var)
            }
            else {
                expect_unit(ctx, ast.expr[true_branch].range, true_branch_var)?;
                write(ir, range, InstrKind::Label { label: else_label });
                Ok(true_branch_var)
            }
        }
        &ast::ExprKind::WhileLoop { condition, body } => {
            let (start_label, then_label, else_label) = (ctx.label(), ctx.label(), ctx.label());
            write(ir, range, InstrKind::Label { label: start_label });

            let condition_var = check_expr(ctx, scope, ir, ast, loop_info, condition)?;
            expect_boolean(ctx, ast.expr[condition].range, condition_var)?;

            write(ir, range, InstrKind::ConditionalJump { condition_var, then_label, else_label });
            write(ir, range, InstrKind::Label { label: then_label });

            let mut loop_info = Some(LoopInfo::default());
            let (body_var, layer) =
                with_scope(scope, |scope| check_expr(ctx, scope, ir, ast, &mut loop_info, body))?;
            ctx.diagnostics.extend(unused_variable_warnings(&layer));
            expect_unit(ctx, ast.expr[body].range, body_var)?;
            write(ir, range, InstrKind::Jump { target_label: start_label });

            if let Some(LoopInfo { break_offsets, continue_offsets }) = loop_info {
                for break_offset in break_offsets {
                    patch(ir, break_offset, InstrKind::Jump { target_label: else_label });
                }
                for continue_offset in continue_offsets {
                    patch(ir, continue_offset, InstrKind::Jump { target_label: start_label });
                }
            }

            write(ir, range, InstrKind::Label { label: else_label });
            Ok(ctx.constants.unit_var)
        }
        ast::ExprKind::Break { result: Some(_) } => {
            todo!()
        }
        ast::ExprKind::Break { result: None } => {
            if let Some(loop_info) = loop_info {
                loop_info.break_offsets.push(write(ir, range, InstrKind::Placeholder));
                Ok(diverge(ctx, scope))
            }
            else {
                Err(db::Diagnostic::error(range, "Break outside of a loop"))
            }
        }
        ast::ExprKind::Continue => {
            if let Some(loop_info) = loop_info {
                loop_info.continue_offsets.push(write(ir, range, InstrKind::Placeholder));
                Ok(diverge(ctx, scope))
            }
            else {
                Err(db::Diagnostic::error(range, "Continue outside of a loop"))
            }
        }
        &ast::ExprKind::UnaryCall { operand, operator: op @ ast::UnaryOp::Negate } => {
            let dst_var = ctx.var(ir, ctx.constants.integer_type);
            let argument = check_expr(ctx, scope, ir, ast, loop_info, operand)?;
            expect_integer(ctx, ast.expr[operand].range, argument)?;
            write(ir, range, InstrKind::Call {
                dst_var,
                fn_var: (ctx.arena.var)
                    .push(ir::Variable::builtin(ctx.constants.unit_type, ir::Builtin::UnOp(op))),
                arg_vars: vec![argument],
            });
            Ok(dst_var)
        }
        &ast::ExprKind::UnaryCall { operand, operator: op @ ast::UnaryOp::LogicNot } => {
            let dst_var = ctx.var(ir, ctx.constants.boolean_type);
            let argument = check_expr(ctx, scope, ir, ast, loop_info, operand)?;
            expect_boolean(ctx, ast.expr[operand].range, argument)?;
            write(ir, range, InstrKind::Call {
                dst_var,
                fn_var: (ctx.arena.var)
                    .push(ir::Variable::builtin(ctx.constants.unit_type, ir::Builtin::UnOp(op))),
                arg_vars: vec![argument],
            });
            Ok(dst_var)
        }
        &ast::ExprKind::InfixCall { left, right, operator: ast::BinaryOp::Assign } => {
            let ast::ExprKind::Variable { name } = &ast.expr[left].kind
            else {
                let message = "The left-hand side of an assignment must be an identifier";
                return Err(db::Diagnostic::error(ast.expr[left].range, message));
            };
            let dst_var = lookup_variable(scope, name)?;
            let src_var = check_expr(ctx, scope, ir, ast, loop_info, right)?;
            write(ir, range, InstrKind::Copy { src_var, dst_var });
            Ok(ctx.constants.unit_var)
        }
        &ast::ExprKind::InfixCall { left, right, operator: ast::BinaryOp::LogicAnd } => {
            let (continue_label, break_label, exit_label) = (ctx.label(), ctx.label(), ctx.label());
            let dst_var = ctx.var(ir, ctx.constants.boolean_type);
            let lhs = check_expr(ctx, scope, ir, ast, loop_info, left)?;
            expect_boolean(ctx, ast.expr[left].range, lhs)?;
            write(ir, range, InstrKind::ConditionalJump {
                condition_var: lhs,
                then_label: continue_label,
                else_label: break_label,
            });
            write(ir, range, InstrKind::Label { label: continue_label });
            let rhs = check_expr(ctx, scope, ir, ast, loop_info, right)?;
            expect_boolean(ctx, ast.expr[right].range, rhs)?;
            write(ir, range, InstrKind::Copy { src_var: rhs, dst_var });
            write(ir, range, InstrKind::Jump { target_label: exit_label });
            write(ir, range, InstrKind::Label { label: break_label });
            write(ir, range, InstrKind::Constant { value: 0, dst_var });
            write(ir, range, InstrKind::Label { label: exit_label });
            Ok(dst_var)
        }
        &ast::ExprKind::InfixCall { left, right, operator: ast::BinaryOp::LogicOr } => {
            let (continue_label, break_label, exit_label) = (ctx.label(), ctx.label(), ctx.label());
            let dst_var = ctx.var(ir, ctx.constants.boolean_type);
            let lhs = check_expr(ctx, scope, ir, ast, loop_info, left)?;
            expect_boolean(ctx, ast.expr[left].range, lhs)?;
            write(ir, range, InstrKind::ConditionalJump {
                condition_var: lhs,
                then_label: break_label,
                else_label: continue_label,
            });
            write(ir, range, InstrKind::Label { label: continue_label });
            let rhs = check_expr(ctx, scope, ir, ast, loop_info, right)?;
            expect_boolean(ctx, ast.expr[right].range, rhs)?;
            write(ir, range, InstrKind::Copy { src_var: rhs, dst_var });
            write(ir, range, InstrKind::Jump { target_label: exit_label });
            write(ir, range, InstrKind::Label { label: break_label });
            write(ir, range, InstrKind::Constant { value: 1, dst_var });
            write(ir, range, InstrKind::Label { label: exit_label });
            Ok(dst_var)
        }
        &ast::ExprKind::InfixCall {
            left,
            right,
            operator:
                op @ (ast::BinaryOp::Add
                | ast::BinaryOp::Subtract
                | ast::BinaryOp::Multiply
                | ast::BinaryOp::Divide
                | ast::BinaryOp::Modulo),
        } => {
            let dst_var = ctx.var(ir, ctx.constants.integer_type);
            let lhs = check_expr(ctx, scope, ir, ast, loop_info, left)?;
            expect_integer(ctx, ast.expr[left].range, lhs)?;
            let rhs = check_expr(ctx, scope, ir, ast, loop_info, right)?;
            expect_integer(ctx, ast.expr[right].range, rhs)?;
            write(ir, range, InstrKind::Call {
                dst_var,
                fn_var: (ctx.arena.var)
                    .push(ir::Variable::builtin(ctx.constants.unit_type, ir::Builtin::BinOp(op))),
                arg_vars: vec![lhs, rhs],
            });
            Ok(dst_var)
        }
        &ast::ExprKind::InfixCall {
            left,
            right,
            operator:
                op @ (ast::BinaryOp::Less
                | ast::BinaryOp::LessEqual
                | ast::BinaryOp::Greater
                | ast::BinaryOp::GreaterEqual),
        } => {
            let dst_var = ctx.var(ir, ctx.constants.boolean_type);
            let lhs = check_expr(ctx, scope, ir, ast, loop_info, left)?;
            expect_integer(ctx, ast.expr[left].range, lhs)?;
            let rhs = check_expr(ctx, scope, ir, ast, loop_info, right)?;
            expect_integer(ctx, ast.expr[right].range, rhs)?;
            write(ir, range, InstrKind::Call {
                dst_var,
                fn_var: (ctx.arena.var)
                    .push(ir::Variable::builtin(ctx.constants.unit_type, ir::Builtin::BinOp(op))),
                arg_vars: vec![lhs, rhs],
            });
            Ok(dst_var)
        }
        &ast::ExprKind::InfixCall {
            left,
            right,
            operator: op @ (ast::BinaryOp::EqualEqual | ast::BinaryOp::NotEqual),
        } => {
            let dst_var = ctx.var(ir, ctx.constants.boolean_type);

            let lhs = check_expr(ctx, scope, ir, ast, loop_info, left)?;
            let rhs = check_expr(ctx, scope, ir, ast, loop_info, right)?;

            expect_type_eq(ctx, range, ctx.arena.var[lhs].typ, ctx.arena.var[rhs].typ)?;

            write(ir, range, InstrKind::Call {
                dst_var,
                fn_var: (ctx.arena.var)
                    .push(ir::Variable::builtin(ctx.constants.unit_type, ir::Builtin::BinOp(op))),
                arg_vars: vec![lhs, rhs],
            });

            Ok(dst_var)
        }
        ast::ExprKind::FunctionCall { function, arguments } => {
            let function_var = check_expr(ctx, scope, ir, ast, loop_info, *function)?;
            let function_type = ctx.arena.var[function_var].typ;
            let ir::Type::Function { params, ret: return_type } =
                ctx.arena.typ[function_type].clone()
            else {
                let message = format!(
                    "Expected a function type, but found {}",
                    function_type.display(&ctx.arena)
                );
                return Err(db::Diagnostic::error(ast.expr[*function].range, message));
            };
            if params.len() != arguments.len() {
                let message = format!(
                    "Function has {} parameters, but {} arguments were given",
                    params.len(),
                    arguments.len()
                );
                return Err(db::Diagnostic::error(range, message));
            }
            let arguments = std::iter::zip(params.iter(), arguments.iter())
                .map(|(&param, &arg)| {
                    let arg_var = check_expr(ctx, scope, ir, ast, loop_info, arg)?;
                    expect_type_eq(ctx, ast.expr[arg].range, param, ctx.arena.var[arg_var].typ)?;
                    Ok(arg_var)
                })
                .collect::<db::Result<_>>()?;
            let dst_var = ctx.var(ir, return_type);
            write(ir, range, InstrKind::Call {
                dst_var,
                fn_var: function_var,
                arg_vars: arguments,
            });
            Ok(dst_var)
        }
    }
}

fn check_type(ctx: &mut Context, ast: &ast::Arena, typ: ast::TypeId) -> db::Result<ir::TypeId> {
    match &ast.typ[typ].kind {
        ast::TypeKind::Variable { name } => match name.string.as_str() {
            "Int" => Ok(ctx.constants.integer_type),
            "Bool" => Ok(ctx.constants.boolean_type),
            "Unit" => Ok(ctx.constants.unit_type),
            unknown => {
                Err(db::Diagnostic::error(ast.typ[typ].range, format!("Unknown type: {unknown}")))
            }
        },
        ast::TypeKind::Function { params, ret } => {
            let ret = check_type(ctx, ast, *ret)?;
            let params: Vec<ir::TypeId> =
                params.iter().map(|&typ| check_type(ctx, ast, typ)).collect::<db::Result<_>>()?;
            Ok(ctx.arena.typ.push(ir::Type::Function { params, ret }))
        }
    }
}

fn check_function(
    ctx: &mut Context,
    scope: &mut Scope,
    ast: &ast::Arena,
    function: &ast::Function,
) -> db::Result<ir::Function> {
    let (ir, layer) = with_scope(scope, |scope| {
        let ret = (function.return_type)
            .map_or(Ok(ctx.constants.unit_type), |typ| check_type(ctx, ast, typ))?;
        let mut ir = ir::Function {
            name: function.name.clone(),
            typ: ctx.constants.unit_type, // Real type assigned below
            return_type: ret,
            instructions: Vec::new(),
            locals: 0,
            params: function.parameters.len(),
            asm: None,
        };
        let mut params = Vec::new();

        for param in function.parameters.iter().take(6) {
            let typ = check_type(ctx, ast, param.typ)?;
            let var = ctx.var(&mut ir, typ);
            scope.top().bind(param.name.clone(), var);
            params.push(typ);
        }

        for (index, param) in function.parameters.iter().skip(6).enumerate() {
            let typ = check_type(ctx, ast, param.typ)?;
            let var = ctx.arena.var.push(ir::Variable::local(typ, (index + 2) as isize * 8));
            scope.top().bind(param.name.clone(), var);
            params.push(typ);
        }

        ir.typ = ctx.arena.typ.push(ir::Type::Function { params, ret });
        let body = check_expr(ctx, scope, &mut ir, ast, &mut None, function.body)?;
        expect_type_eq(ctx, ast.expr[function.body].range, ret, ctx.arena.var[body].typ)?;
        write(&mut ir, ast.expr[function.body].range, InstrKind::Return { var: body });
        Ok(ir)
    })?;
    ctx.diagnostics.extend(unused_variable_warnings(&layer));
    Ok(ir)
}

fn make_builtin(
    ctx: &mut Context,
    name: &str,
    asm: Vec<&'static str>,
    return_type: ir::TypeId,
    params: Vec<ir::TypeId>,
) -> ir::Function {
    ir::Function {
        locals: 0,
        params: params.len(),
        name: db::Name::builtin(name),
        typ: ctx.arena.typ.push(ir::Type::Function { params, ret: return_type }),
        instructions: Vec::new(),
        return_type,
        asm: Some(asm),
    }
}

// TODO: move to codegen.rs
fn builtins(ctx: &mut Context) -> Vec<ir::Function> {
    vec![
        make_builtin(
            ctx,
            "read_int",
            vec![
                "\tmovq $int_scan_format, %rdi",
                "\tleaq -8(%rbp), %rsi",
                "\tcallq scanf",
                "\tmovq -8(%rbp), %rax",
            ],
            ctx.constants.integer_type,
            Vec::new(),
        ),
        make_builtin(
            ctx,
            "print_int",
            vec!["\tmovq %rdi, %rsi", "\tmovq $int_print_format, %rdi", "\tcallq printf"],
            ctx.constants.unit_type,
            vec![ctx.constants.integer_type],
        ),
        make_builtin(
            ctx,
            "print_bool",
            vec![
                "\tcmpq $0, %rdi",
                "\tjne .Ltrue",
                "\tmovq $bool_false_string, %rdi",
                "\tjmp .Lprint_bool",
                ".Ltrue:",
                "\tmovq $bool_true_string, %rdi",
                ".Lprint_bool:",
                "\tcallq puts",
            ],
            ctx.constants.unit_type,
            vec![ctx.constants.boolean_type],
        ),
    ]
}

fn register_function(ctx: &mut Context, scope: &mut Scope, function: &ir::Function, index: usize) {
    let var = ir::Variable { typ: function.typ, kind: ir::VariableKind::Function { index } };
    scope.bottom().bind(function.name.clone(), ctx.arena.var.push(var));
}

fn check_main(
    ctx: &mut Context,
    scope: &mut Scope,
    module: &ast::Module,
) -> db::Result<ir::Function> {
    let mut main = ir::Function {
        name: db::Name::builtin("main"),
        typ: ctx.constants.unit_type,
        return_type: ctx.constants.unit_type,
        instructions: Vec::new(),
        locals: 0,
        params: 0,
        asm: None,
    };

    let (result, layer) = with_scope(scope, |scope| {
        for &effect in &module.effects {
            let dst = check_expr(ctx, scope, &mut main, &module.arena, &mut None, effect)?;
            discard(ctx, dst, module.arena.expr[effect].range);
        }
        check_expr(ctx, scope, &mut main, &module.arena, &mut None, module.result)
    })?;
    ctx.diagnostics.extend(unused_variable_warnings(&layer));

    match &ctx.arena.typ[ctx.arena.var[result].typ] {
        ir::Type::Integer => {
            write(&mut main, db::Range::default(), InstrKind::Call {
                dst_var: ctx.constants.unit_var,
                fn_var: lookup_variable(scope, &db::Name::builtin("print_int"))?,
                arg_vars: vec![result],
            });
        }
        ir::Type::Boolean => {
            write(&mut main, db::Range::default(), InstrKind::Call {
                dst_var: ctx.constants.unit_var,
                fn_var: lookup_variable(scope, &db::Name::builtin("print_bool"))?,
                arg_vars: vec![result],
            });
        }
        _ => {}
    }

    Ok(main)
}

pub fn typecheck(module: ast::Module) -> db::Result<ir::Program> {
    let mut ctx = Context::new();
    let mut functions = Vec::new();
    let mut scope = Scope::default();

    scope.stack.push(ScopeLayer::default());
    for function in builtins(&mut ctx) {
        register_function(&mut ctx, &mut scope, &function, functions.len());
        functions.push(function);
    }

    for function in &module.functions {
        let function = check_function(&mut ctx, &mut scope, &module.arena, function)?;
        register_function(&mut ctx, &mut scope, &function, functions.len());
        functions.push(function);
        scope.stack.resize_with(1, ScopeLayer::default);
    }

    functions.push(check_main(&mut ctx, &mut scope, &module)?);
    Ok(ir::Program { functions, arena: ctx.arena, diagnostics: ctx.diagnostics })
}
