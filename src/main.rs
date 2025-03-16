#![allow(unused_parens, dead_code)]
#![feature(trait_alias, let_chains)]

mod ast;
mod codegen;
mod db;
mod indexvec;
mod ir;
mod lex;
mod parse;
mod poschars;
mod typecheck;
mod util;

use serde_json::{Value as Json, json};

#[derive(PartialEq, Eq, Debug, serde::Deserialize)]
#[serde(tag = "command")]
enum Request {
    #[serde(rename = "ping")]
    Ping,
    #[serde(rename = "compile")]
    Compile { code: String },
}

#[derive(Debug, serde::Serialize)]
struct Error {
    #[serde(rename = "error")]
    message: String,
}

impl<T: ToString> From<T> for Error {
    fn from(value: T) -> Self {
        Self { message: value.to_string() }
    }
}

fn compile(id: usize, code: &str) -> Result<String, Error> {
    let program = typecheck::typecheck(parse::parse(code).map_err(|diag| {
        Error::from(format!("{}-{}: {}", diag.range.begin, diag.range.end, diag.message))
    })?);

    use std::process::{Command, Stdio};
    let mut child = Command::new("/bin/sh")
        .arg("-c")
        .arg("mkdir -p \"$1\" && cd \"$1\" && gcc -x assembler -g -no-pie -o program - && base64 program")
        .arg("--")
        .arg(format!("/tmp/compilers-project/{id}"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;

    codegen::codegen(&mut child.stdin.take().unwrap(), &program)?;

    if child.wait()?.success() {
        Ok(std::io::read_to_string(child.stdout.take().unwrap())?)
    }
    else {
        Err(Error::from(std::io::read_to_string(child.stderr.take().unwrap())?))
    }
}

fn handle(id: usize, reader: impl std::io::Read) -> Result<Json, Error> {
    match serde_json::from_reader(reader)? {
        Request::Ping => Ok(json!({})),
        Request::Compile { code } => compile(id, &code).map(|base64| json!({ "program": base64 })),
    }
}

fn serve(id: usize, stream: std::net::TcpStream) {
    eprintln!("Serving client {id}.");
    match handle(id, &stream) {
        Ok(reply) => serde_json::to_writer(stream, &reply).expect("Failed to serialize reply"),
        Err(error) => serde_json::to_writer(stream, &error).expect("Failed to serialize error"),
    }
    eprintln!("Finished serving client {id}.");
}

fn socket(port: u16) -> std::net::SocketAddr {
    use std::net::{IpAddr, Ipv4Addr, SocketAddr};
    SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), port)
}

fn listen(listener: std::net::TcpListener) {
    for (id, incoming) in listener.incoming().enumerate() {
        match incoming {
            Ok(stream) => {
                std::thread::spawn(move || serve(id, stream));
            }
            Err(error) => {
                eprintln!("Could not establish TCP connection: {error}. Ignoring.");
            }
        }
    }
}

fn main() -> std::io::Result<()> {
    if std::env::args().nth(1).is_some_and(|arg| arg == "serve") {
        let port = 3000;
        match std::net::TcpListener::bind(socket(port)) {
            Ok(listener) => {
                eprintln!("Listening on port {port}");
                listen(listener);
                unreachable!()
            }
            Err(error) => {
                eprintln!("Could not bind to port {port}: {error}");
                std::process::exit(1)
            }
        }
    }
    else {
        let code = std::fs::read_to_string("test-program")?;
        let program = typecheck::typecheck(parse::parse(&code).unwrap());
        codegen::codegen(&mut std::io::stdout(), &program)?;
        for db::Diagnostic { message, range, severity } in &program.diagnostics {
            eprintln!("{:?} {}-{}: {}", severity, range.begin, range.end, message);
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn request(str: &str) -> Request {
        serde_json::from_str(str).unwrap()
    }

    #[test]
    fn deserialize() {
        assert_eq!(request(r#"{"command": "ping"}"#), Request::Ping);
        assert_eq!(
            request(r#"{"command": "compile", "code": "source code text"}"#),
            Request::Compile { code: String::from("source code text") }
        );
    }
}
