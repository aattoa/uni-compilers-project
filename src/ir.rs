use crate::indexvec::IndexVec;
use crate::{db, define_index};

define_index!(pub TypeId);
define_index!(pub VarId);

#[derive(Clone, Debug)]
pub enum InstrKind {
    Constant {
        value: i64,
        destination: VarId,
    },
    Copy {
        source: VarId,
        destination: VarId,
    },
    Call {
        destination: VarId,
        function: VarId,
        arguments: Vec<VarId>,
    },
    Return {
        value: VarId,
    },
    Jump {
        target_offset: usize,
    },
    ConditionalJump {
        condition: VarId,
        then_offset: usize,
        else_offset: usize,
    },
    Placeholder,
}

#[derive(Clone, Debug)]
pub struct Instruction {
    pub kind: InstrKind,
    pub range: db::Range,
}

#[derive(Clone, Debug)]
pub enum Type {
    Integer,
    Boolean,
    Unit,
    Never,
    Function { params: Vec<TypeId>, ret: TypeId },
}

#[derive(Clone, Debug)]
pub struct Function {
    pub name: db::Name,
    pub return_type: TypeId,
    pub instructions: Vec<Instruction>,
}

#[derive(Default)]
pub struct Arena {
    pub typ: IndexVec<Type, TypeId>,
    pub var: IndexVec<TypeId, VarId>,
}

pub struct Constants {
    pub integer_type: TypeId,
    pub boolean_type: TypeId,
    pub unit_type: TypeId,
    pub unit_var: VarId,
}

pub struct Program {
    pub functions: Vec<Function>,
    pub arena: Arena,
    pub diagnostics: Vec<db::Diagnostic>,
}

impl Constants {
    pub fn new(arena: &mut Arena) -> Self {
        let integer_type = arena.typ.push(Type::Integer);
        let boolean_type = arena.typ.push(Type::Boolean);
        let unit_type = arena.typ.push(Type::Unit);
        let unit_var = arena.var.push(unit_type);
        Self { integer_type, boolean_type, unit_type, unit_var }
    }
}

pub trait ArenaDisplay {
    fn display(self, arena: &Arena) -> impl std::fmt::Display;
}

impl ArenaDisplay for TypeId {
    fn display(self, arena: &Arena) -> impl std::fmt::Display {
        TypeDisplay { id: self, arena }
    }
}

#[derive(Clone, Copy)]
pub struct TypeDisplay<'a> {
    pub id: TypeId,
    pub arena: &'a Arena,
}

impl std::fmt::Display for TypeDisplay<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self.arena.typ[self.id] {
            Type::Integer => write!(f, "Int"),
            Type::Boolean => write!(f, "Bool"),
            Type::Unit => write!(f, "Unit"),
            Type::Never => write!(f, "!"),
            Type::Function { params, ret } => {
                write!(f, "(")?;
                let mut params = params.iter();
                if let Some(param) = params.next() {
                    write!(f, "{}", param.display(self.arena))?;
                    for param in params {
                        write!(f, ", {}", param.display(self.arena))?;
                    }
                }
                write!(f, ") => {}", ret.display(self.arena))
            }
        }
    }
}
