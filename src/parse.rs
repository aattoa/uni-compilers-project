use crate::lex::{Lexer, Token, TokenKind};
use crate::{ast, db};

pub type ParseResult<T> = Result<T, db::Diagnostic>;

struct Context<'a> {
    arena: ast::Arena,
    lexer: Lexer<'a>,
    document: &'a str,
}

impl<'a> Context<'a> {
    fn new(document: &'a str) -> Self {
        Self { arena: ast::Arena::default(), lexer: Lexer::new(document), document }
    }
    fn current_range(&mut self) -> db::Range {
        if let Some(token) = self.lexer.peek() {
            token.range
        }
        else {
            db::Range::for_position(self.lexer.position())
        }
    }
    fn error(&mut self, message: impl Into<String>) -> db::Diagnostic {
        db::Diagnostic::error(self.current_range(), message)
    }
    fn expected(&mut self, description: impl std::fmt::Display) -> db::Diagnostic {
        let found = self.lexer.peek().map_or("the end of input", |token| token.kind.show());
        self.error(format!("Expected {description}, but found {found}"))
    }
    fn expect(&mut self, kind: TokenKind) -> ParseResult<Token> {
        if let Some(token) = self.lexer.next_if_kind(kind) {
            Ok(token)
        }
        else {
            Err(self.expected(kind.show()))
        }
    }
    fn consume(&mut self, kind: TokenKind) -> bool {
        self.lexer.next_if_kind(kind).is_some()
    }
    fn name(&mut self, token: Token) -> ast::NameId {
        debug_assert!(token.kind == TokenKind::Identifier);
        self.arena.add_name(token.view.string(self.document))
    }
}

trait Parser<T> = Fn(&mut Context) -> ParseResult<Option<T>>;

fn extract<T>(ctx: &mut Context, parser: impl Parser<T>, desc: &str) -> ParseResult<T> {
    parser(ctx)?.ok_or_else(|| ctx.expected(desc))
}

fn extract_sequence<T>(ctx: &mut Context, elem: impl Parser<T>, desc: &str) -> ParseResult<Vec<T>> {
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
    token.kind == TokenKind::Identifier && token.view.string(document) == word
}

fn parse_word(ctx: &mut Context, word: &str) -> bool {
    ctx.lexer.next_if(|token| is_word(token, word, ctx.document)).is_some()
}

fn extract_word(ctx: &mut Context, word: &str) -> ParseResult<()> {
    if parse_word(ctx, word) { Ok(()) } else { Err(ctx.expected(format!("keyword '{word}'"))) }
}

fn parse_name(ctx: &mut Context) -> Option<ast::NameId> {
    ctx.lexer.next_if_kind(TokenKind::Identifier).map(|token| ctx.name(token))
}

fn extract_name(ctx: &mut Context) -> ParseResult<ast::NameId> {
    ctx.expect(TokenKind::Identifier).map(|token| ctx.name(token))
}

fn extract_integer(token: Token, ctx: &mut Context) -> ParseResult<ast::Expr> {
    match token.view.string(ctx.document).parse() {
        Ok(literal) => Ok(ast::Expr::Integer { literal }),
        Err(error) => Err(db::Diagnostic::error(token.range, error.to_string())),
    }
}

fn extract_block(_open: Token, ctx: &mut Context) -> ParseResult<ast::Expr> {
    let mut expressions = Vec::new();
    while let Some(expr) = parse_expr(ctx)? {
        expressions.push(expr);
        if !ctx.consume(TokenKind::Semicolon) {
            break;
        }
    }
    ctx.expect(TokenKind::BraceClose)?;
    Ok(ast::Expr::Block { expressions })
}

fn extract_declaration(_var: Token, ctx: &mut Context) -> ParseResult<ast::Expr> {
    let name = extract_name(ctx)?;
    let typ = parse_type_annotation(ctx)?;
    ctx.expect(TokenKind::Equal)?;
    let initializer = extract(ctx, parse_expr, "an initializer")?;
    Ok(ast::Expr::Declaration { name, typ, initializer })
}

fn extract_while(_while: Token, ctx: &mut Context) -> ParseResult<ast::Expr> {
    let condition = extract(ctx, parse_expr, "a condition")?;
    extract_word(ctx, "do")?;
    let body = extract(ctx, parse_expr, "a loop body")?;
    Ok(ast::Expr::WhileLoop { condition, body })
}

fn extract_conditional(_open: Token, ctx: &mut Context) -> ParseResult<ast::Expr> {
    let condition = extract(ctx, parse_expr, "a condition")?;
    extract_word(ctx, "then")?;
    let true_branch = extract(ctx, parse_expr, "the true branch")?;
    let false_branch = if parse_word(ctx, "else") {
        Some(extract(ctx, parse_expr, "the false branch")?)
    }
    else {
        None
    };
    Ok(ast::Expr::Conditional { condition, true_branch, false_branch })
}

fn extract_unary(operator: ast::UnaryOp, ctx: &mut Context) -> ParseResult<ast::Expr> {
    extract(ctx, parse_expr, "an operand").map(|operand| ast::Expr::UnaryCall { operand, operator })
}

fn extract_identifier(token: Token, ctx: &mut Context) -> ParseResult<ast::Expr> {
    match token.view.string(ctx.document) {
        "var" => extract_declaration(token, ctx),
        "if" => extract_conditional(token, ctx),
        "while" => extract_while(token, ctx),
        "not" => extract_unary(ast::UnaryOp::LogicNot, ctx),
        "true" => Ok(ast::Expr::Boolean { literal: true }),
        "false" => Ok(ast::Expr::Boolean { literal: false }),
        "return" => Ok(ast::Expr::Return { result: parse_expr(ctx)? }),
        "break" => Ok(ast::Expr::Break { result: parse_expr(ctx)? }),
        "continue" => Ok(ast::Expr::Continue),
        name => Ok(ast::Expr::Variable { name: ctx.arena.add_name(name) }),
    }
}

fn extract_paren(_open: Token, ctx: &mut Context) -> ParseResult<ast::Expr> {
    let inner = extract(ctx, parse_expr, "the inner expression")?;
    ctx.expect(TokenKind::ParenClose)?;
    Ok(ast::Expr::Parenthesized { inner })
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
        TokenKind::Identifier => match token.view.string(ctx.document) {
            "and" => Some(LogicAnd),
            "or" => Some(LogicOr),
            _ => None,
        },
        _ => None,
    }
}

fn parse_normal_expr(ctx: &mut Context) -> ParseResult<Option<ast::Expr>> {
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

fn parse_infix_call(ctx: &mut Context, precedence: usize) -> ParseResult<Option<ast::ExprId>> {
    if precedence == OPERATORS.len() {
        parse_normal_expr(ctx).map(|expr| expr.map(|expr| ctx.arena.expr.push(expr)))
    }
    else {
        let mut lhs = parse_infix_call(ctx, precedence + 1)?;
        if let Some(lhs) = &mut lhs {
            while let Some(token) = ctx.lexer.next() {
                if let Some(operator) = binary_op(token, ctx)
                    && OPERATORS[precedence].contains(&operator)
                {
                    let rhs =
                        extract(ctx, |ctx| parse_infix_call(ctx, precedence + 1), "an operand")?;
                    *lhs = ctx.arena.expr.push(ast::Expr::InfixCall {
                        left: *lhs,
                        right: rhs,
                        operator,
                    });
                }
                else {
                    ctx.lexer.unlex(token);
                    break;
                }
            }
        }
        Ok(lhs)
    }
}

fn parse_expr(ctx: &mut Context) -> ParseResult<Option<ast::ExprId>> {
    let lhs = parse_infix_call(ctx, 0)?;
    if let Some(lhs) = lhs
        && ctx.consume(TokenKind::Equal)
    {
        let rhs = extract(ctx, parse_expr, "an operand")?;
        Ok(Some(ctx.arena.expr.push(ast::Expr::InfixCall {
            left: lhs,
            right: rhs,
            operator: ast::BinaryOp::Assign,
        })))
    }
    else {
        Ok(lhs)
    }
}

fn extract_function_type(_open: Token, ctx: &mut Context) -> ParseResult<ast::TypeId> {
    let parameter_types = extract_sequence(ctx, parse_type, "a type")?;
    ctx.expect(TokenKind::ParenClose)?;
    ctx.expect(TokenKind::RightArrow)?;
    let return_type = extract(ctx, parse_type, "a return type")?;
    Ok(ctx.arena.typ.push(ast::Type::Function { parameter_types, return_type }))
}

fn extract_typename(token: Token, ctx: &mut Context) -> ParseResult<ast::TypeId> {
    let name = ctx.name(token);
    Ok(ctx.arena.typ.push(ast::Type::Variable { name }))
}

fn parse_type(ctx: &mut Context) -> ParseResult<Option<ast::TypeId>> {
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

fn parse_type_annotation(ctx: &mut Context) -> ParseResult<Option<ast::TypeId>> {
    if ctx.consume(TokenKind::Colon) {
        extract(ctx, parse_type, "a type").map(Some)
    }
    else {
        Ok(None)
    }
}

fn parse_parameter(ctx: &mut Context) -> ParseResult<Option<ast::Parameter>> {
    if let Some(name) = parse_name(ctx) {
        extract(ctx, parse_type_annotation, "a type annotation")
            .map(|typ| Some(ast::Parameter { name, typ }))
    }
    else {
        Ok(None)
    }
}

fn extract_function(ctx: &mut Context) -> ParseResult<ast::Function> {
    let name = extract_name(ctx)?;
    ctx.expect(TokenKind::ParenOpen)?;
    let parameters = extract_sequence(ctx, parse_parameter, "a parameter")?;
    ctx.expect(TokenKind::ParenClose)?;
    let return_type = parse_type_annotation(ctx)?;
    let body = extract_block(ctx.expect(TokenKind::BraceOpen)?, ctx)?;
    Ok(ast::Function { name, parameters, return_type, body: ctx.arena.expr.push(body) })
}

fn parse_top_level(ctx: &mut Context) -> ParseResult<Option<ast::TopLevel>> {
    if parse_word(ctx, "fun") {
        extract_function(ctx).map(|func| Some(ast::TopLevel::Func(ctx.arena.func.push(func))))
    }
    else {
        parse_expr(ctx).map(|expr| expr.map(ast::TopLevel::Expr))
    }
}

pub fn parse(document: &str) -> ParseResult<ast::Module> {
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

    fn assert_name(arena: &ast::Arena, expr: ast::ExprId, str: &str) {
        assert_let!(ast::Expr::Variable { name } = arena.expr[expr]);
        assert_eq!(arena.name[name], str);
    }
    fn assert_typename(arena: &ast::Arena, typ: ast::TypeId, str: &str) {
        assert_let!(ast::Type::Variable { name } = arena.typ[typ]);
        assert_eq!(arena.name[name], str);
    }

    fn top_level_expr<'a>(top_level: &'a [ast::TopLevel], arena: &'a ast::Arena) -> &'a ast::Expr {
        assert_let!([ast::TopLevel::Expr(expr_id)] = top_level);
        &arena.expr[*expr_id]
    }

    #[test]
    fn conditional() {
        let ast::Module { top_level, arena } = parse("if a then b else c").unwrap();
        assert_let!(
            ast::Expr::Conditional { condition, true_branch, false_branch } =
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
            ast::Expr::Declaration { name, typ, initializer } = top_level_expr(&top_level, &arena)
        );
        assert_eq!(arena.name[*name], "a");
        assert_name(&arena, *initializer, "b");
        assert_let!(ast::Type::Function { ref parameter_types, return_type } =
            arena.typ[typ.unwrap()]);
        assert_eq!(parameter_types.len(), 2);
        assert_typename(&arena, parameter_types[0], "A");
        assert_typename(&arena, parameter_types[1], "B");
        assert_typename(&arena, return_type, "C");
    }

    #[test]
    fn while_loop() {
        let ast::Module { top_level, arena } = parse("while a do b").unwrap();
        assert_let!(ast::Expr::WhileLoop { condition, body } = top_level_expr(&top_level, &arena));
        assert_name(&arena, *condition, "a");
        assert_name(&arena, *body, "b");
    }

    #[test]
    fn precedence() {
        {
            let ast::Module { top_level, arena } = parse("a + b * c or d and e - f").unwrap(); // ((a + (b * c)) or (d and (e - f)))

            assert_let!(
                ast::Expr::InfixCall { left, right, operator: ast::BinaryOp::LogicOr } =
                    top_level_expr(&top_level, &arena)
            );

            {
                assert_let!(ast::Expr::InfixCall { left, right, operator } = arena.expr[*left]);
                assert_eq!(operator, ast::BinaryOp::Add);
                assert_name(&arena, left, "a");
                assert_let!(ast::Expr::InfixCall { left, right, operator } = arena.expr[right]);
                assert_eq!(operator, ast::BinaryOp::Multiply);
                assert_name(&arena, left, "b");
                assert_name(&arena, right, "c");
            }
            {
                assert_let!(ast::Expr::InfixCall { left, right, operator } = arena.expr[*right]);
                assert_eq!(operator, ast::BinaryOp::LogicAnd);
                assert_name(&arena, left, "d");
                assert_let!(ast::Expr::InfixCall { left, right, operator } = arena.expr[right]);
                assert_eq!(operator, ast::BinaryOp::Subtract);
                assert_name(&arena, left, "e");
                assert_name(&arena, right, "f");
            }
        }
        {
            let ast::Module { top_level, arena } = parse("return a - b + c").unwrap(); // (return ((a - b) + c))
            assert_let!(ast::Expr::Return { result } = top_level_expr(&top_level, &arena));
            assert_let!(
                ast::Expr::InfixCall { left, right, operator: ast::BinaryOp::Add } =
                    arena.expr[result.unwrap()]
            );
            assert_name(&arena, right, "c");
            assert_let!(
                ast::Expr::InfixCall { left, right, operator: ast::BinaryOp::Subtract } =
                    arena.expr[left]
            );
            assert_name(&arena, left, "a");
            assert_name(&arena, right, "b");
        }
        {
            let ast::Module { top_level, arena } = parse("(a + b) * c").unwrap();
            assert_let!(
                ast::Expr::InfixCall { left, right, operator: ast::BinaryOp::Multiply } =
                    top_level_expr(&top_level, &arena)
            );
            assert_name(&arena, *right, "c");
            assert_let!(ast::Expr::Parenthesized { inner } = arena.expr[*left]);
            assert_let!(
                ast::Expr::InfixCall { left, right, operator: ast::BinaryOp::Add } =
                    arena.expr[inner]
            );
            assert_name(&arena, left, "a");
            assert_name(&arena, right, "b");
        }
        {
            let ast::Module { top_level, arena } = parse("a = b = c * d + e").unwrap(); // (a = (b = ((c * d) + e)))
            assert_let!(
                ast::Expr::InfixCall { left, right, operator: ast::BinaryOp::Assign } =
                    top_level_expr(&top_level, &arena)
            );
            assert_name(&arena, *left, "a");
            assert_let!(
                ast::Expr::InfixCall { left, right, operator: ast::BinaryOp::Assign } =
                    arena.expr[*right]
            );
            assert_name(&arena, left, "b");
            assert_let!(
                ast::Expr::InfixCall { left, right, operator: ast::BinaryOp::Add } =
                    arena.expr[right]
            );
            assert_name(&arena, right, "e");
            assert_let!(
                ast::Expr::InfixCall { left, right, operator: ast::BinaryOp::Multiply } =
                    arena.expr[left]
            );
            assert_name(&arena, left, "c");
            assert_name(&arena, right, "d");
        }
    }

    #[test]
    fn function() {
        let ast::Module { top_level, arena } = parse("fun id(x: T): R { return x }").unwrap();
        assert_let!([ast::TopLevel::Func(func_id)] = top_level.as_slice());
        let ast::Function { name, parameters, return_type, body } = &arena.func[*func_id];
        assert_eq!(arena.name[*name], "id");
        assert_typename(&arena, return_type.unwrap(), "R");

        assert_let!([ast::Parameter { name, typ }] = parameters.as_slice());
        assert_eq!(arena.name[*name], "x");
        assert_typename(&arena, *typ, "T");

        assert_let!(ast::Expr::Block { expressions } = &arena.expr[*body]);
        assert_let!([return_id] = expressions.as_slice());
        assert_let!(ast::Expr::Return { result } = arena.expr[*return_id]);
        assert_name(&arena, result.unwrap(), "x");
    }
}
