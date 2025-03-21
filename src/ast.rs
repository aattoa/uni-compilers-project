use crate::indexvec::IndexVec;
use crate::{db, define_index};

define_index!(pub ExprId);
define_index!(pub TypeId);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BinaryOp {
    Assign,
    EqualEqual,
    NotEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    Add,
    Subtract,
    Multiply,
    Divide,
    Modulo,
    LogicAnd,
    LogicOr,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum UnaryOp {
    Negate,
    LogicNot,
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    Integer {
        literal: i64,
    },
    Boolean {
        literal: bool,
    },
    Variable {
        name: db::Name,
    },
    Parenthesized {
        inner: ExprId,
    },
    Declaration {
        name: db::Name,
        typ: Option<TypeId>,
        initializer: ExprId,
    },
    Return {
        result: Option<ExprId>,
    },
    Block {
        effects: Vec<ExprId>,
        result: Option<ExprId>,
    },
    Conditional {
        condition: ExprId,
        true_branch: ExprId,
        false_branch: Option<ExprId>,
    },
    WhileLoop {
        condition: ExprId,
        body: ExprId,
    },
    UnaryCall {
        operand: ExprId,
        operator: UnaryOp,
    },
    InfixCall {
        left: ExprId,
        right: ExprId,
        operator: BinaryOp,
    },
    FunctionCall {
        function: ExprId,
        arguments: Vec<ExprId>,
    },
    Break {
        result: Option<ExprId>,
    },
    Continue,
}

#[derive(Clone, Debug)]
pub enum TypeKind {
    Variable { name: db::Name },
    Function { params: Vec<TypeId>, ret: TypeId },
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub range: db::Range,
}

#[derive(Clone, Debug)]
pub struct Type {
    pub kind: TypeKind,
    pub range: db::Range,
}

#[derive(Clone, Debug)]
pub struct Parameter {
    pub name: db::Name,
    pub typ: TypeId,
}

#[derive(Clone, Debug)]
pub struct Function {
    pub name: db::Name,
    pub parameters: Vec<Parameter>,
    pub return_type: Option<TypeId>,
    pub body: ExprId,
}

#[derive(Default)]
pub struct Arena {
    pub expr: IndexVec<Expr, ExprId>,
    pub typ: IndexVec<Type, TypeId>,
}

pub struct Module {
    pub arena: Arena,
    pub functions: Vec<Function>,
    pub effects: Vec<ExprId>,
    pub result: Option<ExprId>,
}
