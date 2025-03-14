use crate::ast::{self, Expr, ExprId, ExprKind, Type, TypeId, TypeKind};
use crate::db::{self, Diagnostic, Name, Range};
use crate::lex::{Lexer, Token, TokenKind};

struct Context<'a> {
    arena: ast::Arena,
    lexer: Lexer<'a>,
    document: &'a str,
}

impl<'a> Context<'a> {
    fn new(document: &'a str) -> Self {
        Self { arena: ast::Arena::default(), lexer: Lexer::new(document), document }
    }
    fn error(&mut self, message: impl Into<String>) -> Diagnostic {
        Diagnostic::error(self.lexer.current_range(), message)
    }
    fn expected(&mut self, description: impl std::fmt::Display) -> Diagnostic {
        let found = self.lexer.peek().map_or("the end of input", |token| token.kind.show());
        self.error(format!("Expected {description}, but found {found}"))
    }
    fn expect(&mut self, kind: TokenKind) -> db::Result<Token> {
        self.lexer.next_if_kind(kind).ok_or_else(|| self.expected(kind.show()))
    }
    fn consume(&mut self, kind: TokenKind) -> bool {
        self.lexer.next_if_kind(kind).is_some()
    }
    fn name(&mut self, token: Token) -> Name {
        Name { string: token.range.view(self.document).into(), range: token.range }
    }
}

trait Parser<T> = Fn(&mut Context) -> db::Result<Option<T>>;

fn extract<T>(ctx: &mut Context, parser: impl Parser<T>, desc: &str) -> db::Result<T> {
    parser(ctx)?.ok_or_else(|| ctx.expected(desc))
}

fn extract_sequence<T>(ctx: &mut Context, elem: impl Parser<T>, desc: &str) -> db::Result<Vec<T>> {
    let mut vec = Vec::new();
    if let Some(head) = elem(ctx)? {
        vec.push(head);
        while ctx.consume(TokenKind::Comma) {
            vec.push(extract(ctx, &elem, desc)?);
        }
    }
    Ok(vec)
}

fn is_word(token: Token, word: &str, document: &str) -> bool {
    token.kind == TokenKind::Identifier && token.range.view(document) == word
}

fn parse_word(ctx: &mut Context, word: &str) -> bool {
    ctx.lexer.next_if(|token| is_word(token, word, ctx.document)).is_some()
}

fn extract_word(ctx: &mut Context, word: &str) -> db::Result<()> {
    if parse_word(ctx, word) { Ok(()) } else { Err(ctx.expected(format!("keyword '{word}'"))) }
}

fn parse_name(ctx: &mut Context) -> Option<Name> {
    ctx.lexer.next_if_kind(TokenKind::Identifier).map(|token| ctx.name(token))
}

fn extract_name(ctx: &mut Context) -> db::Result<Name> {
    ctx.expect(TokenKind::Identifier).map(|token| ctx.name(token))
}

fn extract_integer(token: Token, ctx: &mut Context) -> db::Result<ExprKind> {
    match token.range.view(ctx.document).parse() {
        Ok(literal) => Ok(ExprKind::Integer { literal }),
        Err(error) => Err(Diagnostic::error(token.range, error.to_string())),
    }
}

fn extract_block(_open: Token, ctx: &mut Context) -> db::Result<ExprKind> {
    let mut effects = Vec::new();
    let mut result = None;
    while let Some(expr) = parse_expr(ctx)? {
        if ctx.consume(TokenKind::Semicolon) {
            effects.push(expr);
        }
        else {
            result = Some(expr);
            break;
        }
    }
    ctx.expect(TokenKind::BraceClose)?;
    Ok(ExprKind::Block { effects, result })
}

fn extract_declaration(_var: Token, ctx: &mut Context) -> db::Result<ExprKind> {
    let name = extract_name(ctx)?;
    let typ = parse_type_annotation(ctx)?;
    ctx.expect(TokenKind::Equal)?;
    let initializer = extract(ctx, parse_expr, "an initializer")?;
    Ok(ExprKind::Declaration { name, typ, initializer })
}

fn extract_while(_while: Token, ctx: &mut Context) -> db::Result<ExprKind> {
    let condition = extract(ctx, parse_expr, "a condition")?;
    extract_word(ctx, "do")?;
    let body = extract(ctx, parse_expr, "a loop body")?;
    Ok(ExprKind::WhileLoop { condition, body })
}

fn extract_conditional(_open: Token, ctx: &mut Context) -> db::Result<ExprKind> {
    let condition = extract(ctx, parse_expr, "a condition")?;
    extract_word(ctx, "then")?;
    let true_branch = extract(ctx, parse_expr, "the true branch")?;
    let false_branch = if parse_word(ctx, "else") {
        Some(extract(ctx, parse_expr, "the false branch")?)
    }
    else {
        None
    };
    Ok(ExprKind::Conditional { condition, true_branch, false_branch })
}

fn extract_unary(operator: ast::UnaryOp, ctx: &mut Context) -> db::Result<ExprKind> {
    let operand = extract(ctx, parse_expr, "an operand")?;
    Ok(ExprKind::UnaryCall { operand, operator })
}

fn extract_identifier(token: Token, ctx: &mut Context) -> db::Result<ExprKind> {
    match token.range.view(ctx.document) {
        "var" => extract_declaration(token, ctx),
        "if" => extract_conditional(token, ctx),
        "while" => extract_while(token, ctx),
        "not" => extract_unary(ast::UnaryOp::LogicNot, ctx),
        "true" => Ok(ExprKind::Boolean { literal: true }),
        "false" => Ok(ExprKind::Boolean { literal: false }),
        "return" => Ok(ExprKind::Return { result: parse_expr(ctx)? }),
        "break" => Ok(ExprKind::Break { result: parse_expr(ctx)? }),
        "continue" => Ok(ExprKind::Continue),
        "new" | "delete" => Err(db::Diagnostic::error(token.range, "Unsupported expression")),
        name => Ok(ExprKind::Variable { name: Name { string: name.into(), range: token.range } }),
    }
}

fn extract_paren(_open: Token, ctx: &mut Context) -> db::Result<ExprKind> {
    let inner = extract(ctx, parse_expr, "the inner expression")?;
    ctx.expect(TokenKind::ParenClose)?;
    Ok(ExprKind::Parenthesized { inner })
}

fn binary_op(token: Token, ctx: &Context) -> Option<ast::BinaryOp> {
    use ast::BinaryOp::*;
    match token.kind {
        TokenKind::EqualEqual => Some(EqualEqual),
        TokenKind::NotEqual => Some(NotEqual),
        TokenKind::Less => Some(Less),
        TokenKind::LessEqual => Some(LessEqual),
        TokenKind::Greater => Some(Greater),
        TokenKind::GreaterEqual => Some(GreaterEqual),
        TokenKind::Plus => Some(Add),
        TokenKind::Minus => Some(Subtract),
        TokenKind::Star => Some(Multiply),
        TokenKind::Slash => Some(Divide),
        TokenKind::Percent => Some(Modulo),
        TokenKind::Identifier => match token.range.view(ctx.document) {
            "and" => Some(LogicAnd),
            "or" => Some(LogicOr),
            _ => None,
        },
        _ => None,
    }
}

fn parse_normal_expr(ctx: &mut Context) -> db::Result<Option<ExprKind>> {
    let Some(token) = ctx.lexer.next()
    else {
        return Ok(None);
    };
    match token.kind {
        TokenKind::Identifier => extract_identifier(token, ctx).map(Some),
        TokenKind::Integer => extract_integer(token, ctx).map(Some),
        TokenKind::BraceOpen => extract_block(token, ctx).map(Some),
        TokenKind::ParenOpen => extract_paren(token, ctx).map(Some),
        TokenKind::Minus => extract_unary(ast::UnaryOp::Negate, ctx).map(Some),
        _ => {
            ctx.lexer.unlex(token);
            Ok(None)
        }
    }
}

fn parse_potential_function_call(function: Expr, ctx: &mut Context) -> db::Result<Expr> {
    if ctx.consume(TokenKind::ParenOpen) {
        let arguments = extract_sequence(ctx, parse_expr, "a function argument")?;
        ctx.expect(TokenKind::ParenClose)?;
        let range = Range { begin: function.range.begin, end: ctx.lexer.current_position() };
        let kind = ExprKind::FunctionCall { function: ctx.arena.expr.push(function), arguments };
        parse_potential_function_call(Expr { kind, range }, ctx)
    }
    else {
        Ok(function)
    }
}

const OPERATORS: &[&[ast::BinaryOp]] = {
    use ast::BinaryOp::*;
    &[
        &[LogicOr],
        &[LogicAnd],
        &[EqualEqual, NotEqual],
        &[Less, LessEqual, Greater, GreaterEqual],
        &[Add, Subtract],
        &[Multiply, Divide, Modulo],
    ]
};

fn combined_range(ctx: &Context, left: ExprId, right: ExprId) -> Range {
    Range { begin: ctx.arena.expr[left].range.begin, end: ctx.arena.expr[right].range.end }
}

fn parse_infix_call(ctx: &mut Context, precedence: usize) -> db::Result<Option<ExprId>> {
    if precedence == OPERATORS.len() {
        let begin = ctx.lexer.current_position();
        Ok(if let Some(kind) = parse_normal_expr(ctx)? {
            let end = ctx.lexer.current_position();
            let function = Expr { kind, range: Range { begin, end } };
            let call = parse_potential_function_call(function, ctx)?;
            Some(ctx.arena.expr.push(call))
        }
        else {
            None
        })
    }
    else {
        let Some(mut lhs) = parse_infix_call(ctx, precedence + 1)?
        else {
            return Ok(None);
        };
        while let Some(token) = ctx.lexer.next() {
            if let Some(operator) = binary_op(token, ctx)
                && OPERATORS[precedence].contains(&operator)
            {
                let rhs = extract(ctx, |ctx| parse_infix_call(ctx, precedence + 1), "an operand")?;
                let kind = ExprKind::InfixCall { left: lhs, right: rhs, operator };
                lhs = ctx.arena.expr.push(Expr { kind, range: combined_range(ctx, lhs, rhs) });
            }
            else {
                ctx.lexer.unlex(token);
                break;
            }
        }
        Ok(Some(lhs))
    }
}

fn parse_expr(ctx: &mut Context) -> db::Result<Option<ExprId>> {
    let left = parse_infix_call(ctx, 0)?;
    if let Some(left) = left
        && ctx.consume(TokenKind::Equal)
    {
        let right = extract(ctx, parse_expr, "an operand")?;
        let kind = ExprKind::InfixCall { left, right, operator: ast::BinaryOp::Assign };
        Ok(Some(ctx.arena.expr.push(Expr { kind, range: combined_range(ctx, left, right) })))
    }
    else {
        Ok(left)
    }
}

fn extract_function_type(open: Token, ctx: &mut Context) -> db::Result<TypeId> {
    let params = extract_sequence(ctx, parse_type, "a type")?;
    ctx.expect(TokenKind::ParenClose)?;
    ctx.expect(TokenKind::RightArrow)?;
    let kind = TypeKind::Function { params, ret: extract(ctx, parse_type, "a return type")? };
    let range = Range { begin: open.range.begin, end: ctx.lexer.current_position() };
    Ok(ctx.arena.typ.push(ast::Type { kind, range }))
}

fn extract_typename(token: Token, ctx: &mut Context) -> db::Result<TypeId> {
    let kind = TypeKind::Variable { name: ctx.name(token) };
    Ok(ctx.arena.typ.push(Type { kind, range: token.range }))
}

fn parse_type(ctx: &mut Context) -> db::Result<Option<TypeId>> {
    let Some(token) = ctx.lexer.next()
    else {
        return Ok(None);
    };
    match token.kind {
        TokenKind::ParenOpen => extract_function_type(token, ctx).map(Some),
        TokenKind::Identifier => extract_typename(token, ctx).map(Some),
        _ => {
            ctx.lexer.unlex(token);
            Ok(None)
        }
    }
}

fn parse_type_annotation(ctx: &mut Context) -> db::Result<Option<TypeId>> {
    if ctx.consume(TokenKind::Colon) {
        extract(ctx, parse_type, "a type").map(Some)
    }
    else {
        Ok(None)
    }
}

fn parse_parameter(ctx: &mut Context) -> db::Result<Option<ast::Parameter>> {
    Ok(if let Some(name) = parse_name(ctx) {
        let typ = extract(ctx, parse_type_annotation, "a type annotation")?;
        Some(ast::Parameter { name, typ })
    }
    else {
        None
    })
}

fn extract_function(ctx: &mut Context) -> db::Result<ast::Function> {
    let name = extract_name(ctx)?;
    ctx.expect(TokenKind::ParenOpen)?;
    let parameters = extract_sequence(ctx, parse_parameter, "a parameter")?;
    ctx.expect(TokenKind::ParenClose)?;
    let return_type = parse_type_annotation(ctx)?;
    let open = ctx.expect(TokenKind::BraceOpen)?;
    let kind = extract_block(open, ctx)?;
    let range = Range { begin: open.range.begin, end: ctx.lexer.current_position() };
    let body = ctx.arena.expr.push(Expr { kind, range });
    Ok(ast::Function { name, parameters, return_type, body })
}

fn parse_top_level(ctx: &mut Context) -> db::Result<Option<ast::TopLevel>> {
    if parse_word(ctx, "fun") {
        extract_function(ctx).map(|func| Some(ast::TopLevel::Func(ctx.arena.func.push(func))))
    }
    else {
        parse_expr(ctx).map(|expr| expr.map(ast::TopLevel::Expr))
    }
}

pub fn parse(document: &str) -> db::Result<ast::Module> {
    let mut ctx = Context::new(document);
    let mut top_level = Vec::new();
    while let Some(item) = parse_top_level(&mut ctx)? {
        top_level.push(item);
        ctx.consume(TokenKind::Semicolon); // Permit trailing semicolons.
    }
    if ctx.lexer.peek().is_none() {
        Ok(ast::Module { top_level, arena: ctx.arena })
    }
    else {
        Err(ctx.expected("a function, a top level expression, or the end of input"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::assert_let;

    fn assert_name(arena: &ast::Arena, expr: ExprId, str: &str) {
        assert_let!(ExprKind::Variable { name } = &arena.expr[expr].kind);
        assert_eq!(name.string, str);
    }
    fn assert_typename(arena: &ast::Arena, typ: TypeId, str: &str) {
        assert_let!(TypeKind::Variable { name } = &arena.typ[typ].kind);
        assert_eq!(name.string, str);
    }
    fn top_level_expr<'a>(top_level: &[ast::TopLevel], arena: &'a ast::Arena) -> &'a ExprKind {
        assert_let!([ast::TopLevel::Expr(expr_id)] = top_level);
        &arena.expr[*expr_id].kind
    }

    #[test]
    fn conditional() {
        let ast::Module { top_level, arena } = parse("if a then b else c").unwrap();
        assert_let!(
            ExprKind::Conditional { condition, true_branch, false_branch } =
                top_level_expr(&top_level, &arena)
        );
        assert_name(&arena, *condition, "a");
        assert_name(&arena, *true_branch, "b");
        assert_name(&arena, false_branch.unwrap(), "c");
    }

    #[test]
    fn declaration() {
        let ast::Module { top_level, arena } = parse("var a: (A, B) => C = b").unwrap();
        assert_let!(
            ExprKind::Declaration { name, typ, initializer } = top_level_expr(&top_level, &arena)
        );
        assert_eq!(name.string, "a");
        assert_name(&arena, *initializer, "b");
        assert_let!(TypeKind::Function { params, ret } = &arena.typ[typ.unwrap()].kind);
        assert_eq!(params.len(), 2);
        assert_typename(&arena, params[0], "A");
        assert_typename(&arena, params[1], "B");
        assert_typename(&arena, *ret, "C");
    }

    #[test]
    fn while_loop() {
        let ast::Module { top_level, arena } = parse("while a do b").unwrap();
        assert_let!(ExprKind::WhileLoop { condition, body } = top_level_expr(&top_level, &arena));
        assert_name(&arena, *condition, "a");
        assert_name(&arena, *body, "b");
    }

    #[test]
    fn precedence() {
        {
            let ast::Module { top_level, arena } = parse("a + b * c or d and e - f").unwrap(); // ((a + (b * c)) or (d and (e - f)))

            assert_let!(
                ExprKind::InfixCall { left, right, operator: ast::BinaryOp::LogicOr } =
                    top_level_expr(&top_level, &arena)
            );

            {
                assert_let!(ExprKind::InfixCall { left, right, operator } = arena.expr[*left].kind);
                assert_eq!(operator, ast::BinaryOp::Add);
                assert_name(&arena, left, "a");
                assert_let!(ExprKind::InfixCall { left, right, operator } = arena.expr[right].kind);
                assert_eq!(operator, ast::BinaryOp::Multiply);
                assert_name(&arena, left, "b");
                assert_name(&arena, right, "c");
            }
            {
                assert_let!(
                    ExprKind::InfixCall { left, right, operator } = arena.expr[*right].kind
                );
                assert_eq!(operator, ast::BinaryOp::LogicAnd);
                assert_name(&arena, left, "d");
                assert_let!(ExprKind::InfixCall { left, right, operator } = arena.expr[right].kind);
                assert_eq!(operator, ast::BinaryOp::Subtract);
                assert_name(&arena, left, "e");
                assert_name(&arena, right, "f");
            }
        }
        {
            let ast::Module { top_level, arena } = parse("return a - b + c").unwrap(); // (return ((a - b) + c))
            assert_let!(ExprKind::Return { result } = top_level_expr(&top_level, &arena));
            assert_let!(
                ExprKind::InfixCall { left, right, operator: ast::BinaryOp::Add } =
                    arena.expr[result.unwrap()].kind
            );
            assert_name(&arena, right, "c");
            assert_let!(
                ExprKind::InfixCall { left, right, operator: ast::BinaryOp::Subtract } =
                    arena.expr[left].kind
            );
            assert_name(&arena, left, "a");
            assert_name(&arena, right, "b");
        }
        {
            let ast::Module { top_level, arena } = parse("(a + b) * c").unwrap();
            assert_let!(
                ExprKind::InfixCall { left, right, operator: ast::BinaryOp::Multiply } =
                    top_level_expr(&top_level, &arena)
            );
            assert_name(&arena, *right, "c");
            assert_let!(ExprKind::Parenthesized { inner } = arena.expr[*left].kind);
            assert_let!(
                ExprKind::InfixCall { left, right, operator: ast::BinaryOp::Add } =
                    arena.expr[inner].kind
            );
            assert_name(&arena, left, "a");
            assert_name(&arena, right, "b");
        }
        {
            let ast::Module { top_level, arena } = parse("a = b = c * d + e").unwrap(); // (a = (b = ((c * d) + e)))
            assert_let!(
                ExprKind::InfixCall { left, right, operator: ast::BinaryOp::Assign } =
                    top_level_expr(&top_level, &arena)
            );
            assert_name(&arena, *left, "a");
            assert_let!(
                ExprKind::InfixCall { left, right, operator: ast::BinaryOp::Assign } =
                    arena.expr[*right].kind
            );
            assert_name(&arena, left, "b");
            assert_let!(
                ExprKind::InfixCall { left, right, operator: ast::BinaryOp::Add } =
                    arena.expr[right].kind
            );
            assert_name(&arena, right, "e");
            assert_let!(
                ExprKind::InfixCall { left, right, operator: ast::BinaryOp::Multiply } =
                    arena.expr[left].kind
            );
            assert_name(&arena, left, "c");
            assert_name(&arena, right, "d");
        }
    }

    #[test]
    fn function_call() {
        {
            let ast::Module { top_level, arena } = parse("f(a, b, c)").unwrap();
            assert_let!(
                ExprKind::FunctionCall { function, arguments } = top_level_expr(&top_level, &arena)
            );
            assert_let!([a, b, c] = arguments.as_slice());
            assert_name(&arena, *function, "f");
            assert_name(&arena, *a, "a");
            assert_name(&arena, *b, "b");
            assert_name(&arena, *c, "c");
        }
        {
            let ast::Module { top_level, arena } = parse("-f(a)(b)").unwrap();
            assert_let!(
                ExprKind::UnaryCall { operand, operator: ast::UnaryOp::Negate } =
                    top_level_expr(&top_level, &arena)
            );
            assert_let!(
                ExprKind::FunctionCall { function, arguments } = &arena.expr[*operand].kind
            );
            assert_let!([b] = arguments.as_slice());
            assert_let!(
                ExprKind::FunctionCall { function, arguments } = &arena.expr[*function].kind
            );
            assert_let!([a] = arguments.as_slice());
            assert_name(&arena, *function, "f");
            assert_name(&arena, *a, "a");
            assert_name(&arena, *b, "b");
        }
    }

    #[test]
    fn function_definition() {
        let ast::Module { top_level, arena } = parse("fun id(x: T): R { x; y; z }").unwrap();
        assert_let!([ast::TopLevel::Func(func_id)] = top_level.as_slice());
        let ast::Function { name, parameters, return_type, body } = &arena.func[*func_id];
        assert_eq!(name.string, "id");
        assert_typename(&arena, return_type.unwrap(), "R");

        assert_let!([ast::Parameter { name, typ }] = parameters.as_slice());
        assert_eq!(name.string, "x");
        assert_typename(&arena, *typ, "T");

        assert_let!(ExprKind::Block { effects, result } = &arena.expr[*body].kind);
        assert_let!([x, y] = effects.as_slice());
        assert_name(&arena, *x, "x");
        assert_name(&arena, *y, "y");
        assert_name(&arena, result.unwrap(), "z");
    }
}
