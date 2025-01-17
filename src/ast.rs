use crate::define_index;
use crate::indexvec::{IndexVec, VecIndex};

define_index!(pub ExprId);
define_index!(pub TypeId);
define_index!(pub NameId);
define_index!(pub FuncId);

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
pub enum Expr {
    Integer {
        literal: i64,
    },
    Boolean {
        literal: bool,
    },
    Variable {
        name: NameId,
    },
    Parenthesized {
        inner: ExprId,
    },
    Declaration {
        name: NameId,
        typ: Option<TypeId>,
        initializer: ExprId,
    },
    Return {
        result: Option<ExprId>,
    },
    Block {
        expressions: Vec<ExprId>,
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
pub enum Type {
    Variable {
        name: NameId,
    },
    Function {
        parameter_types: Vec<TypeId>,
        return_type: TypeId,
    },
}

#[derive(Clone, Debug)]
pub struct Parameter {
    pub name: NameId,
    pub typ: TypeId,
}

#[derive(Clone, Debug)]
pub struct Function {
    pub name: NameId,
    pub parameters: Vec<Parameter>,
    pub return_type: Option<TypeId>,
    pub body: ExprId,
}

#[derive(Clone, Copy, Debug)]
pub enum TopLevel {
    Expr(ExprId),
    Func(FuncId),
}

#[derive(Default)]
pub struct Arena {
    pub expr: IndexVec<Expr, ExprId>,
    pub typ: IndexVec<Type, TypeId>,
    pub name: IndexVec<String, NameId>,
    pub func: IndexVec<Function, FuncId>,
}

pub struct Module {
    pub top_level: Vec<TopLevel>,
    pub arena: Arena,
}

impl Arena {
    pub fn add_name(&mut self, name: &str) -> NameId {
        let old = self.name.underlying.iter().position(|string| string == name);
        old.map_or_else(|| self.name.push(String::from(name)), NameId::new)
    }
}
