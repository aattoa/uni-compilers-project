use crate::ast::{BinaryOp, UnaryOp};
use crate::ir;
use std::io;

const SYMBOL_PREFIX: &str = "compilers_project_symbol_";
const PARAM_REGS: [&str; 6] = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"];

fn codegen_prologue(out: &mut dyn io::Write, locals: usize, params: usize) -> io::Result<()> {
    writeln!(out, "\t# Save the caller's base pointer\n\tpushq %rbp")?;
    writeln!(out, "\t# Set new base pointer\n\tmovq %rsp, %rbp")?;

    for (i, reg) in PARAM_REGS.iter().enumerate().take(params.min(PARAM_REGS.len())) {
        writeln!(out, "\t# Copy parameter from register\n\tmovq %{}, -{}(%rbp)", reg, (i + 1) * 8)?;
    }
    if locals != 0 {
        let space = locals * 8;
        writeln!(out, "\t# Reserve stack space for locals\n\tsubq ${space}, %rsp")?;
    }

    Ok(())
}

fn codegen_epilogue(out: &mut dyn io::Write) -> io::Result<()> {
    writeln!(out, "\t# Restore the old stack pointer\n\tmovq %rbp, %rsp")?;
    writeln!(out, "\t# Restore the old base pointer\n\tpopq %rbp")?;
    writeln!(out, "\t# Return control to caller\n\tret")?;
    Ok(())
}

fn location(program: &ir::Program, var: ir::VarId) -> String {
    match program.arena.var[var].kind {
        ir::VariableKind::Local { frame_offset } => format!("{frame_offset}(%rbp)"),
        ir::VariableKind::Function { index } => {
            format!("${SYMBOL_PREFIX}{}", program.functions[index].name.string)
        }
        ir::VariableKind::Builtin { .. } => unreachable!(),
    }
}

fn codegen_unary_operator(
    out: &mut dyn io::Write,
    program: &ir::Program,
    operator: UnaryOp,
    arguments: &[ir::VarId],
) -> io::Result<()> {
    let &[arg] = arguments
    else {
        unreachable!("Typechecker should catch argument mismatch");
    };
    match operator {
        UnaryOp::Negate => {
            writeln!(out, "\tmovq {}, %rax", location(program, arg))?;
            writeln!(out, "\tnegq %rax")?;
        }
        UnaryOp::LogicNot => {
            writeln!(out, "\tmovq {}, %rax", location(program, arg))?;
            writeln!(out, "\txorq $1, %rax")?;
        }
    };
    Ok(())
}

fn codegen_comparison(
    out: &mut dyn io::Write,
    program: &ir::Program,
    set: &str,
    (lhs, rhs): (ir::VarId, ir::VarId),
) -> io::Result<()> {
    writeln!(out, "\tmovq {}, %rax", location(program, lhs))?;
    writeln!(out, "\tcmpq {}, %rax", location(program, rhs))?;
    writeln!(out, "\t{set} %al")?;
    Ok(())
}

fn codegen_binary_operator(
    out: &mut dyn io::Write,
    program: &ir::Program,
    operator: BinaryOp,
    arguments: &[ir::VarId],
) -> io::Result<()> {
    let &[lhs, rhs] = arguments
    else {
        unreachable!("Typechecker should catch argument mismatch");
    };
    match operator {
        BinaryOp::EqualEqual => codegen_comparison(out, program, "sete", (lhs, rhs))?,
        BinaryOp::NotEqual => codegen_comparison(out, program, "setne", (lhs, rhs))?,
        BinaryOp::Less => codegen_comparison(out, program, "setl", (lhs, rhs))?,
        BinaryOp::LessEqual => codegen_comparison(out, program, "setle", (lhs, rhs))?,
        BinaryOp::Greater => codegen_comparison(out, program, "setg", (lhs, rhs))?,
        BinaryOp::GreaterEqual => codegen_comparison(out, program, "setge", (lhs, rhs))?,

        BinaryOp::Add => {
            writeln!(out, "\tmovq {}, %rax", location(program, lhs))?;
            writeln!(out, "\taddq {}, %rax", location(program, rhs))?;
        }
        BinaryOp::Subtract => {
            writeln!(out, "\tmovq {}, %rax", location(program, lhs))?;
            writeln!(out, "\tsubq {}, %rax", location(program, rhs))?;
        }
        BinaryOp::Multiply => {
            writeln!(out, "\tmovq {}, %rax", location(program, lhs))?;
            writeln!(out, "\timulq {}, %rax", location(program, rhs))?;
        }
        BinaryOp::Divide => {
            writeln!(out, "\tmovq {}, %rax", location(program, lhs))?;
            writeln!(out, "\tcqto")?;
            writeln!(out, "\tidivq {}", location(program, rhs))?;
        }
        BinaryOp::Modulo => {
            writeln!(out, "\tmovq {}, %rax", location(program, lhs))?;
            writeln!(out, "\tcqto")?;
            writeln!(out, "\tidivq {}", location(program, rhs))?;
            writeln!(out, "\tmovq %rdx, %rax")?;
        }
        BinaryOp::LogicAnd | BinaryOp::LogicOr | BinaryOp::Assign => {
            unreachable!("These are special cases")
        }
    };
    Ok(())
}

fn codegen_function_call(
    out: &mut dyn io::Write,
    locals: usize,
    program: &ir::Program,
    function: &str,
    arguments: &[ir::VarId],
) -> io::Result<()> {
    for (var, reg) in arguments.iter().copied().zip(PARAM_REGS) {
        writeln!(out, "\tmovq {}, %{}", location(program, var), reg)?;
    }
    for var in arguments.iter().copied().skip(PARAM_REGS.len()).rev() {
        writeln!(out, "\tpushq {}", location(program, var))?;
    }
    if locals % 2 != 0 {
        writeln!(out, "\tsubq $8, %rsp")?;
    }
    writeln!(out, "\tcallq {function}")?;
    if locals % 2 != 0 {
        writeln!(out, "\taddq $8, %rsp")?;
    }
    let stack_args = arguments.iter().skip(PARAM_REGS.len()).len();
    if stack_args != 0 {
        writeln!(out, "\taddq ${}, %rsp", stack_args * 8)?;
    }
    Ok(())
}

fn codegen_instruction(
    out: &mut dyn io::Write,
    program: &ir::Program,
    function: &ir::Function,
    instruction: &ir::Instruction,
) -> io::Result<()> {
    match &instruction.kind {
        &ir::InstrKind::Constant { value, dst_var } => {
            writeln!(out, "\tmovabsq ${}, %rax", value)?;
            writeln!(out, "\tmovq %rax, {}", location(program, dst_var))?;
        }
        &ir::InstrKind::Copy { src_var, dst_var } => {
            if !program.arena.typ[program.arena.var[src_var].typ].is_zero_sized() {
                writeln!(out, "\tmovq {}, %rax", location(program, src_var))?;
                writeln!(out, "\tmovq %rax, {}", location(program, dst_var))?;
            }
        }
        &ir::InstrKind::Call { dst_var, fn_var, ref arg_vars } => {
            match program.arena.var[fn_var].kind {
                ir::VariableKind::Builtin { tag } => {
                    match tag {
                        ir::Builtin::UnOp(op) => {
                            codegen_unary_operator(out, program, op, arg_vars)?;
                        }
                        ir::Builtin::BinOp(op) => {
                            codegen_binary_operator(out, program, op, arg_vars)?;
                        }
                        ir::Builtin::Unit | ir::Builtin::Never => unreachable!(),
                    };
                }
                ir::VariableKind::Local { frame_offset } => {
                    let fun = format!("*{}(%rbp)", frame_offset);
                    codegen_function_call(out, function.locals, program, &fun, arg_vars)?;
                }
                ir::VariableKind::Function { index } => {
                    let fun = format!("{SYMBOL_PREFIX}{}", program.functions[index].name.string);
                    codegen_function_call(out, function.locals, program, &fun, arg_vars)?;
                }
            };
            if !program.arena.typ[program.arena.var[dst_var].typ].is_zero_sized() {
                writeln!(out, "\tmovq %rax, {}", location(program, dst_var))?;
            }
        }
        &ir::InstrKind::Return { var } => {
            if !program.arena.typ[program.arena.var[var].typ].is_zero_sized() {
                writeln!(out, "\tmovq {}, %rax", location(program, var))?;
            }
            writeln!(out, "\tjmp .Lepilogue_{SYMBOL_PREFIX}{}", function.name.string)?;
        }
        &ir::InstrKind::Label { label } => {
            writeln!(out, ".L{}:", label.index)?;
        }
        &ir::InstrKind::Jump { target_label } => {
            writeln!(out, "\tjmp .L{}", target_label.index)?;
        }
        &ir::InstrKind::ConditionalJump { condition_var, then_label, else_label } => {
            writeln!(out, "\tcmpq $0, {}", location(program, condition_var))?;
            writeln!(out, "\tjne .L{}", then_label.index)?;
            writeln!(out, "\tjmp .L{}", else_label.index)?;
        }
        ir::InstrKind::Placeholder => unreachable!("Placeholder should have been patched out"),
    }
    Ok(())
}

fn codegen_function(
    out: &mut dyn io::Write,
    program: &ir::Program,
    function: &ir::Function,
) -> io::Result<()> {
    if let Some(asm) = &function.asm {
        for line in asm {
            writeln!(out, "{line}")?;
        }
        return writeln!(out, "\tret");
    }
    codegen_prologue(out, function.locals, function.params)?;
    for instruction in &function.instructions {
        writeln!(out, "\t# {:?}", instruction.kind)?;
        codegen_instruction(out, program, function, instruction)?;
    }
    writeln!(out, ".Lepilogue_{SYMBOL_PREFIX}{}:", function.name.string)?;
    codegen_epilogue(out)
}

pub fn codegen(out: &mut dyn io::Write, program: &ir::Program) -> io::Result<()> {
    writeln!(out, ".section .text")?;
    writeln!(out, ".extern printf")?;
    writeln!(out, ".extern scanf")?;
    writeln!(out, ".extern puts")?;

    for function in &program.functions {
        writeln!(out)?;
        writeln!(out, ".global {SYMBOL_PREFIX}{}", function.name.string)?;
        writeln!(out, ".type {SYMBOL_PREFIX}{}, @function", function.name.string)?;
        writeln!(out, "{SYMBOL_PREFIX}{}:", function.name.string)?;
        codegen_function(out, program, function)?;
    }

    writeln!(out, "\n.global main\n.type main, @function\nmain:")?;
    codegen_prologue(out, 0, 0)?;
    writeln!(out, "\t# Call the user-provided main function")?;
    writeln!(out, "\tsubq $8, %rsp")?;
    writeln!(out, "\tcallq {SYMBOL_PREFIX}main")?;
    writeln!(out, "\tmovq $0, %rax")?;
    codegen_epilogue(out)?;

    writeln!(out)?;
    writeln!(out, "int_scan_format: .asciz \"%ld\"")?;
    writeln!(out, "int_print_format: .asciz \"%ld\\n\"")?;
    writeln!(out, "bool_true_string: .asciz \"true\"")?;
    writeln!(out, "bool_false_string: .asciz \"false\"")?;
    Ok(())
}
