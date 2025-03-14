use crate::db::Position;
use std::str::Chars;

/// Like Chars, but peekable and keeps track of position information.
#[derive(Clone)]
pub struct PosChars<'a> {
    pub position: Position,
    chars: Chars<'a>,
    next: Option<char>,
}

impl Iterator for PosChars<'_> {
    type Item = char;
    fn next(&mut self) -> Option<char> {
        self.next.take().or_else(|| self.chars.next()).inspect(|&char| self.position.advance(char))
    }
}

impl<'a> PosChars<'a> {
    pub fn new(string: &'a str) -> Self {
        PosChars { position: Position::default(), chars: string.chars(), next: None }
    }
    pub fn peek(&mut self) -> Option<char> {
        if self.next.is_none() {
            self.next = self.chars.next()
        }
        self.next
    }
    pub fn next_if(&mut self, predicate: impl FnOnce(char) -> bool) -> Option<char> {
        if self.peek().is_some_and(predicate) { self.next() } else { None }
    }
    pub fn next_if_eq(&mut self, char: char) -> Option<char> {
        self.next_if(|c| char == c)
    }
    pub fn starts_with(&self, prefix: &str) -> bool {
        self.clone().take(prefix.chars().count()).eq(prefix.chars())
    }
    pub fn consume(&mut self, char: char) -> bool {
        self.next_if_eq(char).is_some()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn next() {
        let mut chars = PosChars::new("hello");
        assert_eq!(chars.next(), Some('h'));
        assert_eq!(chars.next(), Some('e'));
        assert_eq!(chars.next(), Some('l'));
        assert_eq!(chars.next(), Some('l'));
        assert_eq!(chars.next(), Some('o'));
    }

    #[test]
    fn peek() {
        let mut chars = PosChars::new("hello");
        assert_eq!(chars.peek(), Some('h'));
        assert_eq!(chars.peek(), Some('h'));
        assert_eq!(chars.next(), Some('h'));
        assert_eq!(chars.peek(), Some('e'));
        assert_eq!(chars.peek(), Some('e'));
        assert_eq!(chars.next(), Some('e'));
    }

    #[test]
    fn next_if() {
        let mut chars = PosChars::new("hello");
        assert_eq!(chars.next_if(|_| false), None);
        assert_eq!(chars.next_if(|_| false), None);
        assert_eq!(chars.next_if(|c| c == 'h'), Some('h'));
        assert_eq!(chars.next_if(|_| false), None);
        assert_eq!(chars.next_if(|_| false), None);
        assert_eq!(chars.next_if(|c| c == 'e'), Some('e'));
        assert_eq!(chars.next_if(|c| c == 'l'), Some('l'));
    }
}
