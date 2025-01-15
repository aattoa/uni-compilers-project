#[derive(Clone, Copy, PartialEq, Eq, Default, Debug)]
pub struct Position {
    pub line: u32,
    pub character: u32,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Range {
    pub begin: Position,
    pub end: Position,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct View {
    pub begin: u32,
    pub end: u32,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Severity {
    Error,
    Warning,
    Information,
    Hint,
}

#[derive(Clone, Debug)]
pub struct Diagnostic {
    pub message: String,
    pub range: Range,
    pub severity: Severity,
}

#[derive(Clone, Copy, Debug)]
pub struct Ranged<T> {
    pub value: T,
    pub range: Range,
}

impl View {
    pub fn string(self, str: &str) -> &str {
        &str[(self.begin as usize)..(self.end as usize)]
    }
}

impl Position {
    pub fn advance(&mut self, char: char) {
        if char == '\n' {
            self.line += 1;
            self.character = 0;
        }
        else {
            self.character += 1;
        }
    }
}

impl Range {
    pub fn for_position(begin: Position) -> Self {
        Self { begin, end: Position { character: begin.character + 1, ..begin } }
    }
}

impl Diagnostic {
    pub fn error(range: Range, message: impl Into<String>) -> Self {
        Self { message: message.into(), range, severity: Severity::Error }
    }
}
