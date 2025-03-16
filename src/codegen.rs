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
    // TODO: deduplicate
    match operator {
        BinaryOp::EqualEqual => {
            writeln!(out, "\tmovq {}, %rax", location(program, lhs))?;
            writeln!(out, "\tcmpq {}, %rax", location(program, rhs))?;
            writeln!(out, "\tsete %al")?;
        }
        BinaryOp::NotEqual => {
            writeln!(out, "\tmovq {}, %rax", location(program, lhs))?;
            writeln!(out, "\tcmpq {}, %rax", location(program, rhs))?;
            writeln!(out, "\tsetne %al")?;
        }
        BinaryOp::Less => {
            writeln!(out, "\tmovq {}, %rax", location(program, lhs))?;
            writeln!(out, "\tcmpq {}, %rax", location(program, rhs))?;
            writeln!(out, "\tsetl %al")?;
        }
        BinaryOp::LessEqual => {
            writeln!(out, "\tmovq {}, %rax", location(program, lhs))?;
            writeln!(out, "\tcmpq {}, %rax", location(program, rhs))?;
            writeln!(out, "\tsetle %al")?;
        }
        BinaryOp::Greater => {
            writeln!(out, "\tmovq {}, %rax", location(program, lhs))?;
            writeln!(out, "\tcmpq {}, %rax", location(program, rhs))?;
            writeln!(out, "\tsetg %al")?;
        }
        BinaryOp::GreaterEqual => {
            writeln!(out, "\tmovq {}, %rax", location(program, lhs))?;
            writeln!(out, "\tcmpq {}, %rax", location(program, rhs))?;
            writeln!(out, "\tsetge %al")?;
        }
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
                    for (var, reg) in arg_vars.iter().copied().zip(PARAM_REGS) {
                        writeln!(out, "\tmovq {}, %{}", location(program, var), reg)?;
                    }
                    for var in arg_vars.iter().copied().skip(PARAM_REGS.len()).rev() {
                        writeln!(out, "\tpushq {}", location(program, var))?;
                    }
                    writeln!(out, "\tcallq *{}(%rbp)", frame_offset)?;
                }
                ir::VariableKind::Function { index } => {
                    for (var, reg) in arg_vars.iter().copied().zip(PARAM_REGS) {
                        writeln!(out, "\tmovq {}, %{}", location(program, var), reg)?;
                    }
                    for var in arg_vars.iter().copied().skip(PARAM_REGS.len()).rev() {
                        writeln!(out, "\tpushq {}", location(program, var))?;
                    }
                    writeln!(
                        out,
                        "\tcallq {SYMBOL_PREFIX}{}",
                        program.functions[index].name.string
                    )?;
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
    writeln!(out, "\tcallq {SYMBOL_PREFIX}main")?;
    codegen_epilogue(out)?;

    writeln!(out)?;
    writeln!(out, "int_scan_format: .asciz \"%ld\"")?;
    writeln!(out, "int_print_format: .asciz \"%ld\\n\"")?;
    writeln!(out, "bool_true_string: .asciz \"true\"")?;
    writeln!(out, "bool_false_string: .asciz \"false\"")?;
    Ok(())
}
