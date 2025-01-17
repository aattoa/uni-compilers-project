use crate::db;
use crate::poschars::PosChars;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TokenKind {
    Identifier,
    Integer,
    ParenOpen,
    ParenClose,
    BraceOpen,
    BraceClose,
    Comma,
    Colon,
    Semicolon,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Equal,
    EqualEqual,
    NotEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    RightArrow,
    Error,
}

#[derive(Clone, Copy, Debug)]
pub struct Token {
    pub kind: TokenKind,
    pub view: db::View,
    pub range: db::Range,
}

pub struct Lexer<'a> {
    chars: PosChars<'a>,
    next: Option<Token>,
}

fn next_token(char: char, chars: &mut PosChars) -> TokenKind {
    match char {
        '(' => TokenKind::ParenOpen,
        ')' => TokenKind::ParenClose,
        '{' => TokenKind::BraceOpen,
        '}' => TokenKind::BraceClose,
        ',' => TokenKind::Comma,
        ':' => TokenKind::Colon,
        ';' => TokenKind::Semicolon,
        '+' => TokenKind::Plus,
        '-' => TokenKind::Minus,
        '*' => TokenKind::Star,
        '/' => TokenKind::Slash,
        '%' => TokenKind::Percent,

        '!' => (if chars.consume('=') { TokenKind::NotEqual } else { TokenKind::Error }),
        '<' => (if chars.consume('=') { TokenKind::Less } else { TokenKind::LessEqual }),
        '>' => (if chars.consume('=') { TokenKind::Greater } else { TokenKind::GreaterEqual }),

        '=' => {
            if chars.consume('=') {
                TokenKind::EqualEqual
            }
            else if chars.consume('>') {
                TokenKind::RightArrow
            }
            else {
                TokenKind::Equal
            }
        }

        _ if char.is_ascii_alphabetic() || char == '_' => {
            while chars.next_if(|char| char.is_ascii_alphanumeric() || char == '_').is_some() {}
            TokenKind::Identifier
        }
        _ if char.is_ascii_digit() => {
            while chars.next_if(|char| char.is_ascii_digit()).is_some() {}
            TokenKind::Integer
        }
        _ => TokenKind::Error,
    }
}

fn skip_trivia(chars: &mut PosChars) {
    loop {
        while chars.next_if(|char| char.is_ascii_whitespace()).is_some() {}
        if chars.starts_with("//") {
            while chars.next().is_some_and(|char| char != '\n') {}
        }
        else {
            break;
        }
    }
}

fn lex(chars: &mut PosChars) -> Option<Token> {
    skip_trivia(chars);
    let (o1, p1) = (chars.offset, chars.position);
    let kind = next_token(chars.next()?, chars);
    let (o2, p2) = (chars.offset, chars.position);
    Some(Token {
        kind,
        view: db::View { begin: o1, end: o2 },
        range: db::Range { begin: p1, end: p2 },
    })
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Token;
    fn next(&mut self) -> Option<Token> {
        self.next.take().or_else(|| lex(&mut self.chars))
    }
}

impl<'a> Lexer<'a> {
    pub fn new(document: &'a str) -> Self {
        Self { chars: PosChars::new(document), next: None }
    }
    pub fn position(&self) -> db::Position {
        self.chars.position
    }
    pub fn peek(&mut self) -> Option<Token> {
        if self.next.is_none() {
            self.next = lex(&mut self.chars);
        }
        self.next
    }
    pub fn next_if(&mut self, predicate: impl FnOnce(Token) -> bool) -> Option<Token> {
        match self.peek() {
            Some(token) if predicate(token) => self.next(),
            _ => None,
        }
    }
    pub fn next_if_kind(&mut self, kind: TokenKind) -> Option<Token> {
        self.next_if(|token| token.kind == kind)
    }
    pub fn unlex(&mut self, token: Token) {
        assert!(self.next.is_none());
        self.next = Some(token);
    }
}

impl TokenKind {
    pub fn show(self) -> &'static str {
        match self {
            TokenKind::Identifier => "an identifier",
            TokenKind::Integer => "an integer",
            TokenKind::ParenOpen => "an opening parenthesis",
            TokenKind::ParenClose => "a closing parenthesis",
            TokenKind::BraceOpen => "an opening brace",
            TokenKind::BraceClose => "a closing brace",
            TokenKind::Comma => "a comma",
            TokenKind::Colon => "a colon",
            TokenKind::Semicolon => "a semicolon",
            TokenKind::Plus => "a plus sign",
            TokenKind::Minus => "a minus sign",
            TokenKind::Star => "an asterisk",
            TokenKind::Slash => "a slash",
            TokenKind::Percent => "a percent sign",
            TokenKind::Equal => "an equals sign",
            TokenKind::EqualEqual => "a double equals sign",
            TokenKind::NotEqual => "a not equals sign",
            TokenKind::Less => "a less-than sign",
            TokenKind::LessEqual => "a less-than-or-equal-to sign",
            TokenKind::Greater => "a greater-than sign",
            TokenKind::GreaterEqual => "a greater-than-or-equal-to sign",
            TokenKind::RightArrow => "a right arrow",
            TokenKind::Error => "a lexical error",
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basics() {
        let document = "if  3\nwhile";
        let mut lexer = Lexer::new(document);

        let token = lexer.next().unwrap();
        assert_eq!(token.kind, TokenKind::Identifier);
        assert_eq!(token.view.string(document), "if");
        assert_eq!(token.range.begin, db::Position { line: 0, character: 0 });
        assert_eq!(token.range.end, db::Position { line: 0, character: 2 });

        let token = lexer.next().unwrap();
        assert_eq!(token.kind, TokenKind::Integer);
        assert_eq!(token.view.string(document), "3");
        assert_eq!(token.range.begin, db::Position { line: 0, character: 4 });
        assert_eq!(token.range.end, db::Position { line: 0, character: 5 });

        let token = lexer.next().unwrap();
        assert_eq!(token.kind, TokenKind::Identifier);
        assert_eq!(token.view.string(document), "while");
        assert_eq!(token.range.begin, db::Position { line: 1, character: 0 });
        assert_eq!(token.range.end, db::Position { line: 1, character: 5 });

        assert!(lexer.next().is_none());
    }

    fn token_strings(document: &str) -> Vec<&str> {
        Lexer::new(document).map(|token| token.view.string(document)).collect()
    }

    #[test]
    fn example() {
        assert_eq!(
            token_strings("if a <= bee then print_int(123)"),
            vec!["if", "a", "<=", "bee", "then", "print_int", "(", "123", ")"]
        );
    }

    #[test]
    fn operators() {
        assert_eq!(
            token_strings("+ - * / = == != < <= > >= // + - * / = == != < <= > >="),
            vec!["+", "-", "*", "/", "=", "==", "!=", "<", "<=", ">", ">="]
        );
    }

    #[test]
    fn comments() {
        assert_eq!(
            token_strings("aaa // bbb\n\t\t   // qwerty\n      ccc\n// ddd\n// eee"),
            vec!["aaa", "ccc"]
        );
    }
}
