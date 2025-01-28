#![allow(unused_parens, dead_code)]
#![feature(trait_alias, let_chains)]

mod ast;
mod db;
mod indexvec;
mod ir;
mod lex;
mod parse;
mod poschars;
mod typecheck;
mod util;

fn main() -> db::Result<()> {
    let code = std::fs::read_to_string("test-program").unwrap();
    let program = typecheck::typecheck(parse::parse(&code)?);
    for function in &program.functions {
        println!("Function {}:", function.name.string);
        for (offset, instruction) in function.instructions.iter().enumerate() {
            println!("{}: {:?}", offset, instruction.kind);
        }
    }
    for db::Diagnostic { message, range, severity } in &program.diagnostics {
        println!("{:?} {}-{} | {}", severity, range.begin, range.end, message);
    }
    Ok(())
}
