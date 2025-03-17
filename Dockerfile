FROM rust:1.85.0-slim

COPY Cargo.toml Cargo.toml
COPY src src

RUN apt-get update && apt-get install musl-tools --assume-yes && cargo build --release

CMD ["./target/release/project", "serve"]
