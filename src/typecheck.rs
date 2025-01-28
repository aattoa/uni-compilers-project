use crate::ir::{self, ArenaDisplay, InstrKind};
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

struct Scope {
    stack: Vec<ScopeLayer>,
}

struct Context {
    arena: ir::Arena,
    constants: ir::Constants,
    diagnostics: Vec<db::Diagnostic>,
}

impl Scope {
    fn top(&mut self) -> &mut ScopeLayer {
        self.stack.last_mut().unwrap()
    }
    fn bind(&mut self, name: db::Name, var_id: ir::VarId) {
        self.top().bindings.push(Binding { name, var_id, used: false });
    }
}

impl Context {
    fn new() -> Self {
        let mut arena = ir::Arena::default();
        let constants = ir::Constants::new(&mut arena);
        Self { arena, constants, diagnostics: Vec::new() }
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
    expect_type_eq(ctx, range, ctx.constants.unit_type, ctx.arena.var[variable])
}

fn expect_boolean(ctx: &mut Context, range: db::Range, variable: ir::VarId) -> db::Result<()> {
    expect_type_eq(ctx, range, ctx.constants.boolean_type, ctx.arena.var[variable])
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
    let warn = |name: &db::Name| {
        db::Diagnostic::warning(name.range, format!("Unused variable: {}", name.string))
    };
    layer.bindings.iter().filter(|binding| !binding.used).map(move |binding| warn(&binding.name))
}

fn never_var(ctx: &mut Context) -> ir::VarId {
    ctx.arena.var.push(ctx.arena.typ.push(ir::Type::Never))
}

fn write(ir: &mut ir::Function, range: db::Range, kind: InstrKind) -> usize {
    ir.instructions.push(ir::Instruction { kind, range });
    ir.instructions.len() - 1
}

fn patch(ir: &mut ir::Function, offset: usize, kind: InstrKind) {
    debug_assert!(matches!(ir.instructions[offset].kind, ir::InstrKind::Placeholder));
    ir.instructions[offset].kind = kind;
}

fn check_expr(
    ctx: &mut Context,
    scope: &mut Scope,
    ir: &mut ir::Function,
    ast: &ast::Arena,
    expr: ast::ExprId,
) -> db::Result<ir::VarId> {
    let range = ast.expr[expr].range;
    if scope.top().diverged {
        let message = "This expression is unreachable, because the branch has diverged";
        return Err(db::Diagnostic::error(range, message));
    }
    match &ast.expr[expr].kind {
        &ast::ExprKind::Parenthesized { inner } => check_expr(ctx, scope, ir, ast, inner),
        &ast::ExprKind::Integer { literal } => {
            let destination = ctx.arena.var.push(ctx.constants.integer_type);
            write(ir, range, InstrKind::Constant { value: literal, destination });
            Ok(destination)
        }
        &ast::ExprKind::Boolean { literal } => {
            let destination = ctx.arena.var.push(ctx.constants.boolean_type);
            write(ir, range, InstrKind::Constant { value: literal as i64, destination });
            Ok(destination)
        }
        ast::ExprKind::Variable { name } => lookup_variable(scope, name),
        ast::ExprKind::Declaration { name, typ, initializer } => {
            let init = check_expr(ctx, scope, ir, ast, *initializer)?;
            if let &Some(typ) = typ {
                let range = ast.expr[*initializer].range;
                let expected = check_type(ctx, ast, typ)?;
                expect_type_eq(ctx, range, expected, ctx.arena.var[init])?;
            }
            scope.bind(name.clone(), init);
            Ok(ctx.constants.unit_var)
        }
        ast::ExprKind::Block { effects, result } => {
            scope.stack.push(ScopeLayer::default());
            for &effect in effects {
                let destination = check_expr(ctx, scope, ir, ast, effect)?;
                expect_unit(ctx, ast.expr[effect].range, destination)?;
            }
            let result = if let &Some(result) = result {
                check_expr(ctx, scope, ir, ast, result)?
            }
            else {
                ctx.constants.unit_var
            };
            let layer = scope.stack.pop().unwrap();
            ctx.diagnostics.extend(unused_variable_warnings(&layer));
            if layer.diverged { Ok(never_var(ctx)) } else { Ok(result) }
        }
        &ast::ExprKind::Return { result } => {
            if let Some(result) = result {
                let value = check_expr(ctx, scope, ir, ast, result)?;
                expect_type_eq(ctx, ast.expr[result].range, ir.return_type, ctx.arena.var[value])?;
                write(ir, range, InstrKind::Return { value });
            }
            else if matches!(ctx.arena.typ[ir.return_type], ir::Type::Unit) {
                write(ir, range, InstrKind::Return { value: ctx.constants.unit_var });
            }
            else {
                return Err(db::Diagnostic::error(range, "Missing return value"));
            }
            scope.top().diverged = true;
            Ok(never_var(ctx))
        }
        &ast::ExprKind::Conditional { condition: condition_ast, true_branch, false_branch } => {
            let condition = check_expr(ctx, scope, ir, ast, condition_ast)?;
            expect_boolean(ctx, ast.expr[condition_ast].range, condition)?;
            let branch_placeholder = write(ir, range, ir::InstrKind::Placeholder);
            let then_offset = ir.instructions.len();
            let true_branch = check_expr(ctx, scope, ir, ast, true_branch)?;
            if let Some(false_branch) = false_branch {
                let copy_placeholder = write(ir, range, ir::InstrKind::Placeholder);
                let exit_placeholder = write(ir, range, ir::InstrKind::Placeholder);
                let else_offset = ir.instructions.len();
                let false_branch = check_expr(ctx, scope, ir, ast, false_branch)?;
                expect_type_eq(
                    ctx,
                    range,
                    ctx.arena.var[true_branch],
                    ctx.arena.var[false_branch],
                )?;
                let destination = ctx.arena.var.push(ctx.arena.var[true_branch]);
                patch(ir, copy_placeholder, InstrKind::Copy { source: false_branch, destination });
                write(ir, range, InstrKind::Copy { source: false_branch, destination });
                let branch = ir::InstrKind::ConditionalJump { condition, then_offset, else_offset };
                patch(ir, branch_placeholder, branch);
                let skip = ir::InstrKind::Jump { target_offset: ir.instructions.len() };
                patch(ir, exit_placeholder, skip);
                Ok(destination)
            }
            else {
                expect_unit(ctx, range, true_branch)?;
                let else_offset = ir.instructions.len();
                let branch = ir::InstrKind::ConditionalJump { condition, then_offset, else_offset };
                patch(ir, branch_placeholder, branch);
                Ok(ctx.constants.unit_var)
            }
        }
        ast::ExprKind::WhileLoop { condition: _, body: _ } => {
            todo!()
        }
        ast::ExprKind::Break { result: _ } => {
            todo!()
        }
        ast::ExprKind::Continue => {
            todo!()
        }
        ast::ExprKind::UnaryCall { operand: _, operator: _ } => {
            todo!()
        }
        &ast::ExprKind::InfixCall { left, right, operator: ast::BinaryOp::Assign } => {
            let ast::ExprKind::Variable { name } = &ast.expr[left].kind
            else {
                let message = "The left-hand side of an assignment must be an identifier";
                return Err(db::Diagnostic::error(ast.expr[left].range, message));
            };
            let destination = lookup_variable(scope, name)?;
            let source = check_expr(ctx, scope, ir, ast, right)?;
            write(ir, range, InstrKind::Copy { source, destination });
            Ok(ctx.constants.unit_var)
        }
        &ast::ExprKind::InfixCall { left: _, right: _, operator: _ } => {
            todo!()
        }
        ast::ExprKind::FunctionCall { function, arguments } => {
            let function_var = check_expr(ctx, scope, ir, ast, *function)?;
            let function_type = ctx.arena.var[function_var];
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
                    let arg_var = check_expr(ctx, scope, ir, ast, arg)?;
                    expect_type_eq(ctx, ast.expr[arg].range, param, ctx.arena.var[arg_var])?;
                    Ok(arg_var)
                })
                .collect::<db::Result<_>>()?;
            let destination = ctx.arena.var.push(return_type);
            write(ir, range, InstrKind::Call { destination, function: function_var, arguments });
            Ok(destination)
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
            let params =
                params.iter().map(|&typ| check_type(ctx, ast, typ)).collect::<Result<_, _>>()?;
            Ok(ctx.arena.typ.push(ir::Type::Function { params, ret }))
        }
    }
}

fn check_function(
    ctx: &mut Context,
    global: &mut Scope,
    ast: &ast::Arena,
    function: &ast::Function,
) -> db::Result<ir::Function> {
    let return_type = function
        .return_type
        .map_or(Ok(ctx.constants.unit_type), |typ| check_type(ctx, ast, typ))?;
    let mut ir =
        ir::Function { name: function.name.clone(), return_type, instructions: Vec::new() };
    let body = check_expr(ctx, global, &mut ir, ast, function.body)?;
    expect_type_eq(ctx, ast.expr[function.body].range, return_type, ctx.arena.var[body])?;
    Ok(ir)
}

pub fn typecheck(ast::Module { top_level, arena }: ast::Module) -> ir::Program {
    let mut ctx = Context::new();
    let mut functions = Vec::new();

    for top_level in top_level {
        let mut scope = Scope { stack: vec![ScopeLayer::default()] };
        match top_level {
            ast::TopLevel::Expr(expr) => {
                let message = "Top-level expressions are not supported yet";
                ctx.diagnostics.push(db::Diagnostic::error(arena.expr[expr].range, message));
            }
            ast::TopLevel::Func(func) => {
                match check_function(&mut ctx, &mut scope, &arena, &arena.func[func]) {
                    Ok(function) => functions.push(function),
                    Err(diagnostic) => ctx.diagnostics.push(diagnostic),
                }
            }
        }
    }

    ir::Program { functions, arena: ctx.arena, diagnostics: ctx.diagnostics }
}
