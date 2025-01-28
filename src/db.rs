#[derive(Clone, Copy, PartialEq, Eq, Default, Debug)]
pub struct Position {
    pub line: u32,
    pub character: u32,
    pub offset: u32,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Range {
    pub begin: Position,
    pub end: Position,
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

#[derive(Clone, Debug)]
pub struct Name {
    pub string: String,
    pub range: Range,
}

pub type Result<T> = std::result::Result<T, Diagnostic>;

impl Position {
    pub fn advance(&mut self, char: char) {
        if char == '\n' {
            self.line += 1;
            self.character = 0;
        }
        else {
            self.character += 1;
        }
        self.offset += char.len_utf8() as u32;
    }
}

impl std::fmt::Display for Position {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}:{}", self.line + 1, self.character + 1)
    }
}

impl Range {
    pub fn for_position(begin: Position) -> Self {
        Self { begin, end: Position { character: begin.character + 1, ..begin } }
    }
    pub fn view<'a>(&self, str: &'a str) -> &'a str {
        &str[(self.begin.offset as usize)..(self.end.offset as usize)]
    }
}

impl Diagnostic {
    pub fn error(range: Range, message: impl Into<String>) -> Self {
        Self { message: message.into(), range, severity: Severity::Error }
    }
    pub fn warning(range: Range, message: impl Into<String>) -> Self {
        Self { message: message.into(), range, severity: Severity::Warning }
    }
}
