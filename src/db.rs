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
