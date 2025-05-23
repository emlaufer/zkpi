//! IR term definition
//!
//! Generally based on SMT-LIB, and its theories.
//!
//! The most important types and functions are:
//!
//!    * Term structure
//!       * [Term]: perfectly-shared terms. Think of them as shared pointers to
//!       * [TermData]: the underlying term. An operator and some children.
//!       * [Op]: an operator
//!    * Term types
//!       * [Sort]: the type of a term
//!       * [check]: get the type of a term
//!    * Term construction
//!       * [term!]: from an operator and a syntactic list of children
//!       * [leaf_term]: from an operator alone
//!       * [term()]: from an operator and vector of children
//!    * Term data-structures and algorithms
//!       * [TermMap], [TermSet]: maps from and sets of terms
//!       * [PostOrderIter]: an iterator over the descendents of a term. Children-first.
//!    * [Computation]: a collection of variables and assertions about them
//!    * [Value]: a variable-free (and evaluated) term
//!
use crate::util::once::OnceQueue;

use circ_fields::{FieldT, FieldV};
use fxhash::{FxHashMap, FxHashSet};
use hashconsing::{HConsed, WHConsed};
use lazy_static::lazy_static;
use log::debug;
use rug::Integer;
use serde::{de::Visitor, Deserialize, Deserializer, Serialize, Serializer};
use std::collections::BTreeMap;
use std::fmt::{self, Debug, Display, Formatter};
use std::iter::FromIterator;
use std::sync::{Arc, RwLock};

use im::OrdMap;

pub mod bv;
pub mod dist;
pub mod extras;
pub mod precomp;
pub mod text;
pub mod ty;

pub use bv::BitVector;
use extras::PostOrderSkipIter;
pub use ty::{check, check_rec, TypeError, TypeErrorReason};

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
/// An operator
pub enum Op {
    /// a variable
    Var(String, Sort),
    /// a constant
    Const(Value),
    /// a random value
    /// TODO: might be better to merge with var?
    Random(String, Sort),

    /// if-then-else: ternary
    Ite,
    /// equality
    Eq,

    /// bit-vector binary operator
    BvBinOp(BvBinOp),
    /// bit-vector binary predicate
    BvBinPred(BvBinPred),
    /// bit-vector n-ary operator
    BvNaryOp(BvNaryOp),
    /// bit-vector unary operator
    BvUnOp(BvUnOp),
    /// single-bit bit-vector from a boolean
    BoolToBv,
    /// Get bits (high) through (low) from the underlying bit-vector.
    ///
    /// Zero-indexed and inclusive.
    BvExtract(usize, usize),
    /// bit-vector concatenation. n-ary. Low-index arguements map to high-order bits
    BvConcat,
    /// add this many zero bits
    BvUext(usize),
    /// add this many sign-extend bits
    BvSext(usize),
    /// translate a prime-field element into a certain-width bit-vector.
    PfToBv(usize),

    /// boolean implication (binary)
    Implies,
    /// boolean n-ary operator
    BoolNaryOp(BoolNaryOp),
    /// boolean not
    Not,
    /// get this index bit from an input bit-vector
    BvBit(usize),
    // Ternary majority operator.
    /// boolean majority (ternary)
    BoolMaj,

    /// floating-point binary operator
    FpBinOp(FpBinOp),
    /// floating-point binary predicate
    FpBinPred(FpBinPred),
    /// floating-point unary predicate
    FpUnPred(FpUnPred),
    /// floating-point unary operator
    FpUnOp(FpUnOp),
    //FpFma,
    /// cast bit-vector to floating-point, as bits
    BvToFp,
    /// translate the (unsigned) bit-vector number represented by the argument to a floating-point
    /// value of this width.
    UbvToFp(usize),
    /// translate the (signed) bit-vector number represented by the argument to a floating-point
    /// value of this width.
    SbvToFp(usize),
    // dest width
    /// translate the number represented by the argument to a floating-point value of this width.
    FpToFp(usize),

    /// Prime-field unary operator
    PfUnOp(PfUnOp),
    /// Prime-field n-ary operator
    PfNaryOp(PfNaryOp),
    /// Unsigned bit-vector to prime-field
    ///
    /// Takes the modulus.
    UbvToPf(FieldT),

    /// Integer n-ary operator
    IntNaryOp(IntNaryOp),
    /// Integer comparison operator
    IntBinPred(IntBinPred),

    /// Binary operator, with arguments (array, index).
    ///
    /// Gets the value at index in array.
    Select,
    /// Ternary operator, with arguments (array, index, value).
    ///
    /// Makes an array equal to `array`, but with `value` at `index`.
    Store,

    /// Assemble n things into a tuple
    Tuple,
    /// Get the n'th element of a tuple
    Field(usize),
    /// Update (tuple, element)
    Update(usize),

    /// Map (operation)
    Map(Box<Op>),

    /// Call a function (name, argument sorts, return sort)
    Call(String, Vec<Sort>, Sort),

    /// Cyclic right rotation of an array
    /// i.e. (Rot(1) [1,2,3,4]) --> ([4,1,2,3])
    Rot(usize),
    /// Returns the nth smallest of its arguments
    /// May only be used in precomputes
    NthSmallest(usize),
    /// Unary operator, with args array
    ///
    /// Returns the sorted array
    Sort,
    /// Construct array from args.
    Array(Sort, Sort),
    /// Compute Waksman selectors
    Waksman,
}

/// Boolean AND
pub const AND: Op = Op::BoolNaryOp(BoolNaryOp::And);
/// Boolean OR
pub const OR: Op = Op::BoolNaryOp(BoolNaryOp::Or);
/// Boolean XOR
pub const XOR: Op = Op::BoolNaryOp(BoolNaryOp::Xor);
/// Boolean NOT
pub const NOT: Op = Op::Not;
/// Equal to
pub const EQ: Op = Op::Eq;
/// If-then-else
pub const ITE: Op = Op::Ite;
/// Boolean implication
pub const IMPLIES: Op = Op::Implies;
/// Bit-vector AND
pub const BV_AND: Op = Op::BvNaryOp(BvNaryOp::And);
/// Bit-vector OR
pub const BV_OR: Op = Op::BvNaryOp(BvNaryOp::Or);
/// Bit-vector XOR
pub const BV_XOR: Op = Op::BvNaryOp(BvNaryOp::Xor);
/// Bit-vector multiplication
pub const BV_MUL: Op = Op::BvNaryOp(BvNaryOp::Mul);
/// Bit-vector addition
pub const BV_ADD: Op = Op::BvNaryOp(BvNaryOp::Add);
/// Bit-vector subtraction
pub const BV_SUB: Op = Op::BvBinOp(BvBinOp::Sub);
/// Bit-vector unsigned division
pub const BV_UDIV: Op = Op::BvBinOp(BvBinOp::Udiv);
/// Bit-vector unsigned remainder
pub const BV_UREM: Op = Op::BvBinOp(BvBinOp::Urem);
/// Bit-vector shift left
pub const BV_SHL: Op = Op::BvBinOp(BvBinOp::Shl);
/// Bit-vector logical shift right
pub const BV_LSHR: Op = Op::BvBinOp(BvBinOp::Lshr);
/// Bit-vector arithmetic shift right
pub const BV_ASHR: Op = Op::BvBinOp(BvBinOp::Ashr);
/// Bit-vector negation
pub const BV_NEG: Op = Op::BvUnOp(BvUnOp::Neg);
/// Bit-vector not
pub const BV_NOT: Op = Op::BvUnOp(BvUnOp::Not);
/// Bit-vector unsigned less than
pub const BV_ULT: Op = Op::BvBinPred(BvBinPred::Ult);
/// Bit-vector unsigned greater than
pub const BV_UGT: Op = Op::BvBinPred(BvBinPred::Ugt);
/// Bit-vector unsigned less than or equal
pub const BV_ULE: Op = Op::BvBinPred(BvBinPred::Ule);
/// Bit-vector unsigned greater than or equal
pub const BV_UGE: Op = Op::BvBinPred(BvBinPred::Uge);
/// Bit-vector signed less than
pub const BV_SLT: Op = Op::BvBinPred(BvBinPred::Slt);
/// Bit-vector signed greater than
pub const BV_SGT: Op = Op::BvBinPred(BvBinPred::Sgt);
/// Bit-vector signed less than or equal
pub const BV_SLE: Op = Op::BvBinPred(BvBinPred::Sle);
/// Bit-vector signed greater than or equal
pub const BV_SGE: Op = Op::BvBinPred(BvBinPred::Sge);
/// Bit-vector of length one, from boolean
pub const BOOL_TO_BV: Op = Op::BoolToBv;
/// Bit-vector concatenation (high || low). N-ary.
pub const BV_CONCAT: Op = Op::BvConcat;
/// prime-field negation
pub const PF_NEG: Op = Op::PfUnOp(PfUnOp::Neg);
/// prime-field reciprocal
pub const PF_RECIP: Op = Op::PfUnOp(PfUnOp::Recip);
/// prime-field addition
pub const PF_ADD: Op = Op::PfNaryOp(PfNaryOp::Add);
/// prime-field multiplication
pub const PF_MUL: Op = Op::PfNaryOp(PfNaryOp::Mul);
/// integer addition
pub const INT_ADD: Op = Op::IntNaryOp(IntNaryOp::Add);
/// integer multiplication
pub const INT_MUL: Op = Op::IntNaryOp(IntNaryOp::Mul);
/// integer less than
pub const INT_LT: Op = Op::IntBinPred(IntBinPred::Lt);
/// integer less than or equal
pub const INT_LE: Op = Op::IntBinPred(IntBinPred::Le);
/// integer greater than
pub const INT_GT: Op = Op::IntBinPred(IntBinPred::Gt);
/// integer greater than or equal
pub const INT_GE: Op = Op::IntBinPred(IntBinPred::Ge);

impl Op {
    /// Number of arguments for this operator. `None` if n-ary.
    pub fn arity(&self) -> Option<usize> {
        match self {
            Op::Ite => Some(3),
            Op::Eq => Some(2),
            Op::Var(_, _) => Some(0),
            Op::Const(_) => Some(0),
            Op::Random(_, _) => Some(0),
            Op::BvBinOp(_) => Some(2),
            Op::BvBinPred(_) => Some(2),
            Op::BvNaryOp(_) => None,
            Op::BvUnOp(_) => Some(1),
            Op::BoolToBv => Some(1),
            Op::BvExtract(_, _) => Some(1),
            Op::BvConcat => None,
            Op::BvUext(_) => Some(1),
            Op::BvSext(_) => Some(1),
            Op::PfToBv(_) => Some(1),
            Op::Implies => Some(2),
            Op::BoolNaryOp(_) => None,
            Op::Not => Some(1),
            Op::BvBit(_) => Some(1),
            Op::BoolMaj => Some(3),
            Op::FpBinOp(_) => Some(2),
            Op::FpBinPred(_) => Some(2),
            Op::FpUnPred(_) => Some(1),
            Op::FpUnOp(_) => Some(1),
            Op::BvToFp => Some(1),
            Op::UbvToFp(_) => Some(1),
            Op::SbvToFp(_) => Some(1),
            Op::FpToFp(_) => Some(1),
            Op::PfUnOp(_) => Some(1),
            Op::PfNaryOp(_) => None,
            Op::IntNaryOp(_) => None,
            Op::IntBinPred(_) => Some(2),
            Op::UbvToPf(_) => Some(1),
            Op::Select => Some(2),
            Op::Store => Some(3),
            Op::Tuple => None,
            Op::Field(_) => Some(1),
            Op::Update(_) => Some(2),
            Op::Map(op) => op.arity(),
            Op::Call(_, args, _) => Some(args.len()),
            Op::Rot(_) => Some(1),
            Op::NthSmallest(_) => None,
            Op::Sort => Some(1),
            Op::Array(..) => None,
            Op::Waksman => Some(1),
        }
    }
}

impl Display for Op {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Op::Ite => write!(f, "ite"),
            Op::Eq => write!(f, "="),
            Op::Var(n, _) => write!(f, "{}", n),
            Op::Const(c) => write!(f, "{}", c),
            Op::Random(r, _) => write!(f, "rand {}", r),
            Op::BvBinOp(a) => write!(f, "{}", a),
            Op::BvBinPred(a) => write!(f, "{}", a),
            Op::BvNaryOp(a) => write!(f, "{}", a),
            Op::BvUnOp(a) => write!(f, "{}", a),
            Op::BoolToBv => write!(f, "bool2bv"),
            Op::BvExtract(a, b) => write!(f, "(extract {} {})", a, b),
            Op::BvConcat => write!(f, "concat"),
            Op::BvUext(a) => write!(f, "(uext {})", a),
            Op::BvSext(a) => write!(f, "(sext {})", a),
            Op::PfToBv(a) => write!(f, "(pf2bv {})", a),
            Op::Implies => write!(f, "=>"),
            Op::BoolNaryOp(a) => write!(f, "{}", a),
            Op::Not => write!(f, "not"),
            Op::BvBit(a) => write!(f, "(bit {})", a),
            Op::BoolMaj => write!(f, "maj"),
            Op::FpBinOp(a) => write!(f, "{}", a),
            Op::FpBinPred(a) => write!(f, "{}", a),
            Op::FpUnPred(a) => write!(f, "{}", a),
            Op::FpUnOp(a) => write!(f, "{}", a),
            Op::BvToFp => write!(f, "bv2fp"),
            Op::UbvToFp(a) => write!(f, "(ubv2fp {})", a),
            Op::SbvToFp(a) => write!(f, "(sbv2fp {})", a),
            Op::FpToFp(a) => write!(f, "(fp2fp {})", a),
            Op::PfUnOp(a) => write!(f, "{}", a),
            Op::PfNaryOp(a) => write!(f, "{}", a),
            Op::IntNaryOp(a) => write!(f, "{}", a),
            Op::IntBinPred(a) => write!(f, "{}", a),
            Op::UbvToPf(a) => write!(f, "(bv2pf {})", a.modulus()),
            Op::Select => write!(f, "select"),
            Op::Store => write!(f, "store"),
            Op::Tuple => write!(f, "tuple"),
            Op::Field(i) => write!(f, "(field {})", i),
            Op::Update(i) => write!(f, "(update {})", i),
            Op::Map(op) => write!(f, "(map({}))", op),
            Op::Call(name, _, _) => write!(f, "fn:{}", name),
            Op::Rot(i) => write!(f, "(rot {})", i),
            Op::NthSmallest(i) => write!(f, "(nthsmallest {})", i),
            Op::Sort => write!(f, "sort"),
            Op::Array(..) => write!(f, "array"),
            Op::Waksman => write!(f, "waksman"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
/// Boolean n-ary operator
pub enum BoolNaryOp {
    /// Boolean AND
    And,
    /// Boolean XOR
    Xor,
    /// Boolean OR
    Or,
}

impl Display for BoolNaryOp {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            BoolNaryOp::And => write!(f, "and"),
            BoolNaryOp::Or => write!(f, "or"),
            BoolNaryOp::Xor => write!(f, "xor"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
/// Bit-vector binary operator
pub enum BvBinOp {
    /// Bit-vector (-)
    Sub,
    /// Bit-vector (/)
    Udiv,
    /// Bit-vector (%)
    Urem,
    /// Bit-vector (<<)
    Shl,
    /// Bit-vector arithmetic (sign extend) (>>)
    Ashr,
    /// Bit-vector logical (zero fill) (>>)
    Lshr,
}

impl Display for BvBinOp {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            BvBinOp::Sub => write!(f, "bvsub"),
            BvBinOp::Udiv => write!(f, "bvudiv"),
            BvBinOp::Urem => write!(f, "bvurem"),
            BvBinOp::Shl => write!(f, "bvshl"),
            BvBinOp::Ashr => write!(f, "bvashr"),
            BvBinOp::Lshr => write!(f, "bvlshr"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
/// Bit-vector binary predicate
pub enum BvBinPred {
    // TODO: add overflow predicates.
    /// Bit-vector unsigned (<)
    Ult,
    /// Bit-vector unsigned (>)
    Ugt,
    /// Bit-vector unsigned (<=)
    Ule,
    /// Bit-vector unsigned (>=)
    Uge,
    /// Bit-vector signed (<)
    Slt,
    /// Bit-vector signed (>)
    Sgt,
    /// Bit-vector signed (<=)
    Sle,
    /// Bit-vector signed (>=)
    Sge,
}

impl Display for BvBinPred {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            BvBinPred::Ult => write!(f, "bvult"),
            BvBinPred::Ugt => write!(f, "bvugt"),
            BvBinPred::Ule => write!(f, "bvule"),
            BvBinPred::Uge => write!(f, "bvuge"),
            BvBinPred::Slt => write!(f, "bvslt"),
            BvBinPred::Sgt => write!(f, "bvsgt"),
            BvBinPred::Sle => write!(f, "bvsle"),
            BvBinPred::Sge => write!(f, "bvsge"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
/// Bit-vector n-ary operator
pub enum BvNaryOp {
    /// Bit-vector (+)
    Add,
    /// Bit-vector (*)
    Mul,
    /// Bit-vector bitwise OR
    Or,
    /// Bit-vector bitwise AND
    And,
    /// Bit-vector bitwise XOR
    Xor,
}

impl Display for BvNaryOp {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            BvNaryOp::Add => write!(f, "bvadd"),
            BvNaryOp::Mul => write!(f, "bvmul"),
            BvNaryOp::Or => write!(f, "bvor"),
            BvNaryOp::And => write!(f, "bvand"),
            BvNaryOp::Xor => write!(f, "bvxor"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
/// Bit-vector unary operator
pub enum BvUnOp {
    /// Bit-vector bitwise not
    Not,
    /// Bit-vector two's complement negation
    Neg,
}

impl Display for BvUnOp {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            BvUnOp::Not => write!(f, "bvnot"),
            BvUnOp::Neg => write!(f, "bvneg"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
/// Floating-point binary operator
pub enum FpBinOp {
    /// Floating-point (+)
    Add,
    /// Floating-point (*)
    Mul,
    /// Floating-point (-)
    Sub,
    /// Floating-point (/)
    Div,
    /// Floating-point (%)
    Rem,
    /// Floating-point max
    Max,
    /// Floating-point min
    Min,
}

impl Display for FpBinOp {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            FpBinOp::Add => write!(f, "fpadd"),
            FpBinOp::Mul => write!(f, "fpmul"),
            FpBinOp::Sub => write!(f, "fpsub"),
            FpBinOp::Div => write!(f, "fpdiv"),
            FpBinOp::Rem => write!(f, "fprem"),
            FpBinOp::Max => write!(f, "fpmax"),
            FpBinOp::Min => write!(f, "fpmin"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
/// Floating-point unary operator
pub enum FpUnOp {
    /// Floating-point unary negation
    Neg,
    /// Floating-point absolute value
    Abs,
    /// Floating-point square root
    Sqrt,
    /// Floating-point round
    Round,
}

impl Display for FpUnOp {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            FpUnOp::Neg => write!(f, "fpneg"),
            FpUnOp::Abs => write!(f, "fpabs"),
            FpUnOp::Sqrt => write!(f, "fpsqrt"),
            FpUnOp::Round => write!(f, "fpround"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
/// Floating-point binary predicate
pub enum FpBinPred {
    /// Floating-point (<=)
    Le,
    /// Floating-point (<)
    Lt,
    /// Floating-point (=)
    Eq,
    /// Floating-point (>=)
    Ge,
    /// Floating-point (>)
    Gt,
}

impl Display for FpBinPred {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            FpBinPred::Le => write!(f, "fple"),
            FpBinPred::Lt => write!(f, "fplt"),
            FpBinPred::Eq => write!(f, "fpeq"),
            FpBinPred::Ge => write!(f, "fpge"),
            FpBinPred::Gt => write!(f, "fpgt"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
/// Floating-point unary predicate
pub enum FpUnPred {
    /// Is this normal?
    Normal,
    /// Is this subnormal?
    Subnormal,
    /// Is this zero (or negative zero)?
    Zero,
    /// Is this infinite?
    Infinite,
    /// Is this not-a-number?
    Nan,
    /// Is this negative?
    Negative,
    /// Is this positive?
    Positive,
}

impl Display for FpUnPred {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            FpUnPred::Normal => write!(f, "fpnormal"),
            FpUnPred::Subnormal => write!(f, "fpsubnormal"),
            FpUnPred::Zero => write!(f, "fpzero"),
            FpUnPred::Infinite => write!(f, "fpinfinite"),
            FpUnPred::Nan => write!(f, "fpnan"),
            FpUnPred::Negative => write!(f, "fpnegative"),
            FpUnPred::Positive => write!(f, "fppositive"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
/// Finite field n-ary operator
pub enum PfNaryOp {
    /// Finite field (+)
    Add,
    /// Finite field (*)
    Mul,
}

impl Display for PfNaryOp {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            PfNaryOp::Add => write!(f, "+"),
            PfNaryOp::Mul => write!(f, "*"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
/// Finite field n-ary operator
pub enum PfUnOp {
    /// Finite field negation
    Neg,
    /// Finite field reciprocal
    Recip,
}

impl Display for PfUnOp {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            PfUnOp::Neg => write!(f, "-"),
            PfUnOp::Recip => write!(f, "pfrecip"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
/// Integer n-ary operator
pub enum IntNaryOp {
    /// Finite field (+)
    Add,
    /// Finite field (*)
    Mul,
}

impl Display for IntNaryOp {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            IntNaryOp::Add => write!(f, "intadd"),
            IntNaryOp::Mul => write!(f, "intmul"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
/// Integer binary predicate. See [Op::Eq] for equality.
pub enum IntBinPred {
    /// Integer (<)
    Lt,
    /// Integer (>)
    Gt,
    /// Integer (<=)
    Le,
    /// Integer (>=)
    Ge,
}

impl Display for IntBinPred {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            IntBinPred::Lt => write!(f, "<"),
            IntBinPred::Gt => write!(f, ">"),
            IntBinPred::Le => write!(f, "<="),
            IntBinPred::Ge => write!(f, ">="),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
/// A term: an operator applied to arguements
pub struct TermData {
    /// the operator
    pub op: Op,
    /// the arguments
    pub cs: Vec<Term>,
}

impl Display for TermData {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        if self.op.arity() == Some(0) {
            write!(f, "{}", self.op)
        } else {
            write!(f, "({}", self.op)?;
            for c in &self.cs {
                write!(f, " {}", c)?;
            }
            write!(f, ")")
        }
    }
}

impl Debug for TermData {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl Serialize for TermData {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let bytes = text::serialize_term(&mk(self.clone()));
        serializer.serialize_str(&bytes)
    }
}

struct TermDeserVisitor;

impl hashconsing::UniqueConsign for TermData {
    fn unique_make(self) -> Term {
        mk(self)
    }
}

impl<'de> Visitor<'de> for TermDeserVisitor {
    type Value = TermData;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "a string (that textually defines a term)")
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: std::error::Error,
    {
        Ok((*text::parse_term(v.as_bytes())).clone())
    }
}

impl<'de> Deserialize<'de> for TermData {
    fn deserialize<D>(deserializer: D) -> Result<TermData, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_str(TermDeserVisitor)
    }
}

#[derive(Clone, PartialEq, Debug, PartialOrd, Serialize, Deserialize)]
/// An IR value (aka literal)
pub enum Value {
    /// Bit-vector
    BitVector(BitVector),
    /// f32
    F32(f32),
    /// f64
    F64(f64),
    /// Arbitrary-precision integer
    Int(Integer),
    /// Finite field element
    Field(FieldV),
    /// Boolean
    Bool(bool),
    /// Array
    Array(Array),
    /// Tuple
    Tuple(Box<[Value]>),
}

#[derive(Clone, PartialEq, Eq, Debug, PartialOrd, Hash, Serialize, Deserialize)]
/// An IR array value.
///
/// A sized, space array.
pub struct Array {
    /// Key sort
    pub key_sort: Sort,
    /// Default (fill) value. What is stored when a key is missing from the next member
    pub default: Box<Value>,
    /// Key-> Value map
    pub map: OrdMap<Value, Value>,
    /// Size of array. There are this many valid keys.
    pub size: usize,
}

impl Array {
    /// Create a new [Array] from components
    pub fn new(
        key_sort: Sort,
        default: Box<Value>,
        map: OrdMap<Value, Value>,
        size: usize,
    ) -> Self {
        if key_sort.default_value().as_usize().is_none() {
            panic!(
                "IR Arrays cannot have {} index (Int, BitVector, Bool, or Field only)",
                key_sort
            );
        }
        Self {
            key_sort,
            default,
            map,
            size,
        }
    }
    /// Create a new, default-initialized [Array]
    pub fn default(key_sort: Sort, val_sort: &Sort, size: usize) -> Self {
        Self::new(
            key_sort,
            Box::new(val_sort.default_value()),
            Default::default(),
            size,
        )
    }

    // consistency check for index
    fn check_idx(&self, idx: &Value) {
        if idx.sort() != self.key_sort {
            panic!(
                "Tried to index array with key {}, but {} was expected",
                idx.sort(),
                self.key_sort
            );
        }
        match idx.as_usize() {
            Some(idx_u) if idx_u < self.size => (),
            Some(idx_u) => panic!(
                "IR Array out of range: accessed {}, size is {}",
                idx_u, self.size
            ),
            _ => panic!("IR Array index {} not convertible to usize", idx),
        }
    }

    // consistency check for value
    fn check_val(&self, vsrt: Sort) {
        if vsrt != self.default.sort() {
            panic!(
                "Attempted to store {} to an array of {}",
                vsrt,
                self.default.sort()
            );
        }
    }

    /// Store
    pub fn store(mut self, idx: Value, val: Value) -> Self {
        self.check_idx(&idx);
        self.check_val(val.sort());
        self.map.insert(idx, val);
        self
    }

    /// Select
    pub fn select(&self, idx: &Value) -> Value {
        self.check_idx(idx);
        self.map.get(idx).unwrap_or(&*self.default).clone()
    }

    /// Create a new array from a vector
    pub fn from_vec(key_sort: Sort, value_sort: Sort, items: Vec<Value>) -> Self {
        assert!(!items.is_empty());
        let default = value_sort.default_value();
        let size = items.len();
        let map = key_sort.elems_iter_values().zip(items).collect();
        Self::new(key_sort, Box::new(default), map, size)
    }
    /// All values
    pub fn values(&self) -> Vec<Value> {
        self.key_sort
            .elems_iter_values()
            .take(self.size)
            .map(|i| self.select(&i))
            .collect()
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Value::Bool(b) => write!(f, "{}", b),
            Value::F32(b) => write!(f, "{}", b),
            Value::F64(b) => write!(f, "{}", b),
            Value::Int(b) => write!(f, "{}", b),
            Value::Field(b) => write!(f, "{}", b),
            Value::BitVector(b) => write!(f, "{}", b),
            Value::Tuple(fields) => {
                write!(f, "(#t ")?;
                for field in fields.iter() {
                    write!(f, " {}", field)?;
                }
                write!(f, ")")
            }
            Value::Array(a) => write!(f, "{}", a),
        }
    }
}

impl Display for Array {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "(#a {} {} {} (", self.key_sort, self.default, self.size,)?;
        for (k, v) in &self.map {
            write!(f, " ({} {})", k, v)?;
        }
        write!(f, " ))")
    }
}

impl std::cmp::Eq for Value {}
// We walk in danger here, intentionally. One day we may fix it.
// FP is the heart of the problem.
#[allow(clippy::derive_ord_xor_partial_ord)]
impl std::cmp::Ord for Value {
    fn cmp(&self, o: &Self) -> std::cmp::Ordering {
        self.partial_cmp(o).expect("broken Value cmp")
    }
}
// We walk in danger here, intentionally. One day we may fix it.
// FP is the heart of the problem.
#[allow(clippy::derive_hash_xor_eq)]
impl std::hash::Hash for Value {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            Value::BitVector(bv) => bv.hash(state),
            Value::F32(bv) => bv.to_bits().hash(state),
            Value::F64(bv) => bv.to_bits().hash(state),
            Value::Int(bv) => bv.hash(state),
            Value::Field(bv) => bv.hash(state),
            Value::Bool(bv) => bv.hash(state),
            Value::Array(a) => a.hash(state),
            Value::Tuple(s) => {
                s.hash(state);
            }
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, PartialOrd, Ord, Serialize, Deserialize)]
/// The "type" of an IR term
pub enum Sort {
    /// bit-vectors of this width
    BitVector(usize),
    /// f32s
    F32,
    /// f64s
    F64,
    /// arbitrary-precision integer
    Int,
    /// prime field, integers mod FieldT.modulus()
    Field(FieldT),
    /// boolean
    Bool,
    /// Array from one sort to another, of fixed size.
    ///
    /// size presumes an order, and a zero, for the key sort.
    Array(Box<Sort>, Box<Sort>, usize),
    /// A tuple
    Tuple(Box<[Sort]>),
}

impl Sort {
    #[track_caller]
    /// Unwrap the bitsize of this bit-vector, panicking otherwise.
    pub fn as_bv(&self) -> usize {
        if let Sort::BitVector(w) = self {
            *w
        } else {
            panic!("{} is not a bit-vector", self)
        }
    }

    pub fn as_array(&self) -> (Sort, Sort, usize) {
        if let Sort::Array(k, v, s) = self {
            (*k.clone(), *v.clone(), *s)
        } else {
            panic!("{} is not an array", self)
        }
    }

    /// Is this an array?
    pub fn is_array(&self) -> bool {
        matches!(self, Sort::Array(..))
    }

    /// The nth element of this sort.
    /// Only defined for booleans, bit-vectors, and field elements.
    #[track_caller]
    pub fn nth_elem(&self, n: usize) -> Term {
        match self {
            Sort::Bool => {
                assert!(n < 2);
                bool_lit([false, true][n])
            }
            Sort::BitVector(w) => {
                assert!(n < (1 << w));
                bv_lit(n, *w)
            }
            Sort::Field(f) => {
                debug_assert!(&Integer::from(n) < f.modulus());
                pf_lit(f.new_v(n))
            }
            _ => panic!("Can't get nth element of sort {}", self),
        }
    }

    #[track_caller]
    /// Unwrap the modulus of this prime field, panicking otherwise.
    pub fn as_pf(&self) -> Arc<Integer> {
        if let Sort::Field(fty) = self {
            fty.modulus_arc()
        } else {
            panic!("{} is not a field", self)
        }
    }

    #[track_caller]
    /// Unwrap the constituent sorts of this tuple, panicking otherwise.
    pub fn as_tuple(&self) -> &[Sort] {
        if let Sort::Tuple(w) = self {
            w
        } else {
            panic!("{} is not a tuple", self)
        }
    }

    /// An iterator over the elements of this sort (as IR Terms).
    /// Only defined for booleans, bit-vectors, and field elements.
    #[track_caller]
    pub fn elems_iter(&self) -> Box<dyn Iterator<Item = Term>> {
        Box::new(self.elems_iter_values().map(|v| leaf_term(Op::Const(v))))
    }

    /// An iterator over the elements of this sort (as IR values).
    /// Only defined for booleans, bit-vectors, and field elements.
    #[track_caller]
    pub fn elems_iter_values(&self) -> Box<dyn Iterator<Item = Value>> {
        match self {
            Sort::Bool => Box::new([false, true].iter().map(|b| Value::Bool(*b))),
            Sort::BitVector(w) => {
                let w = *w;
                let lim = Integer::from(1) << w as u32;
                Box::new(
                    std::iter::successors(Some(Integer::from(0)), move |p| {
                        let q = p.clone() + 1;
                        if q < lim {
                            Some(q)
                        } else {
                            None
                        }
                    })
                    .map(move |i| Value::BitVector(BitVector::new(i, w))),
                )
            }
            Sort::Field(fty) => {
                let m = fty.modulus_arc();
                let fty = fty.clone();
                Box::new(
                    std::iter::successors(Some(Integer::from(0)), move |p| {
                        let q = p.clone() + 1;
                        if q < *m {
                            Some(q)
                        } else {
                            None
                        }
                    })
                    .map(move |i| Value::Field(fty.new_v(i))),
                )
            }
            _ => panic!("Cannot iterate over {}", self),
        }
    }

    /// Compute the default term for this sort.
    ///
    /// * booleans: false
    /// * bit-vectors: zero
    /// * field elements: zero
    /// * floats: zero
    /// * tuples/arrays: recursively default
    pub fn default_term(&self) -> Term {
        leaf_term(Op::Const(self.default_value()))
    }

    /// Compute the default value for this sort.
    ///
    /// * booleans: false
    /// * bit-vectors: zero
    /// * field elements: zero
    /// * floats: zero
    /// * tuples/arrays: recursively default
    pub fn default_value(&self) -> Value {
        match self {
            Sort::Bool => Value::Bool(false),
            Sort::BitVector(w) => Value::BitVector(BitVector::new(0.into(), *w)),
            Sort::Field(fty) => Value::Field(fty.default_value()),
            Sort::Int => Value::Int(0.into()),
            Sort::F32 => Value::F32(0.0f32),
            Sort::F64 => Value::F64(0.0),
            Sort::Tuple(t) => Value::Tuple(t.iter().map(Sort::default_value).collect()),
            Sort::Array(k, v, n) => Value::Array(Array::default((**k).clone(), v, *n)),
        }
    }

    /// Is this a scalar?
    pub fn is_scalar(&self) -> bool {
        !matches!(self, Sort::Tuple(..) | Sort::Array(..))
    }
}

impl Display for Sort {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Sort::Bool => write!(f, "bool"),
            Sort::BitVector(n) => write!(f, "(bv {})", n),
            Sort::Int => write!(f, "int"),
            Sort::F32 => write!(f, "f32"),
            Sort::F64 => write!(f, "f64"),
            Sort::Field(fty) => write!(f, "(mod {})", fty.modulus()),
            Sort::Array(k, v, n) => write!(f, "(array {} {} {})", k, v, n),
            Sort::Tuple(fields) => {
                write!(f, "(tuple")?;
                for field in fields.iter() {
                    write!(f, " {}", field)?;
                }
                write!(f, ")")
            }
        }
    }
}

/// A (perfectly shared) pointer to a term
pub type Term = HConsed<TermData>;
// "Temporary" terms.
/// A weak (perfectly shared) pointer to a term
pub type TTerm = WHConsed<TermData>;

struct TermTable {
    map: FxHashMap<Arc<TermData>, TTerm>,
    count: u64,
    last_len: usize,
}

impl TermTable {
    fn get(&self, key: &TermData) -> Option<Term> {
        if let Some(old) = self.map.get(key) {
            old.to_hconsed()
        } else {
            None
        }
    }
    fn mk(&mut self, elm: TermData) -> Term {
        // If the element is known and upgradable return it.
        if let Some(hconsed) = self.get(&elm) {
            //debug_assert!(*hconsed.elm == elm);
            return hconsed;
        }
        // Otherwise build hconsed version.
        let elm = Arc::new(elm);
        let hconsed = HConsed {
            elm: elm.clone(),
            uid: self.count,
        };
        // Increment uid count.
        self.count += 1;
        // ...add weak version to the table...
        self.map.insert(elm, hconsed.to_weak());
        // ...and return consed version.
        hconsed
    }
    fn should_collect(&mut self) -> bool {
        let ret = LEN_THRESH_DEN * self.map.len() > LEN_THRESH_NUM * self.last_len;
        if self.last_len > TERM_CACHE_LIMIT {
            // when last_len is big, force a garbage collect every once in a while
            self.last_len = (self.last_len * LEN_DECAY_NUM) / LEN_DECAY_DEN;
        }
        ret
    }
    fn collect(&mut self) {
        let old_size = self.map.len();
        let mut to_check: OnceQueue<Term> = OnceQueue::new();
        self.map.retain(|key, _| {
            if Arc::strong_count(key) > 1 {
                true
            } else {
                to_check.extend(key.cs.iter().cloned());
                false
            }
        });
        while let Some(t) = to_check.pop() {
            let okv = self.map.get_key_value(&*t.elm);
            std::mem::drop(t);
            if let Some((key, _)) = okv {
                if Arc::strong_count(key) <= 1 {
                    to_check.extend(key.cs.iter().cloned());
                    let key = key.clone();
                    self.map.remove(&key);
                }
            }
        }
        let new_size = self.map.len();
        for (k, v) in self.map.iter() {
            assert!(v.elm.upgrade().is_some(), "Can not upgrade: {:?}", k)
        }
        debug!(target: "ir::term::gc", "{} of {} terms collected", old_size - new_size, old_size);
        self.last_len = new_size;
    }
}
struct TypeTable {
    map: FxHashMap<TTerm, Sort>,
}
impl std::ops::Deref for TypeTable {
    type Target = FxHashMap<TTerm, Sort>;
    fn deref(&self) -> &Self::Target {
        &self.map
    }
}
impl std::ops::DerefMut for TypeTable {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.map
    }
}
impl TypeTable {
    fn collect(&mut self) {
        let old_size = self.map.len();
        self.map.retain(|term, _| term.elm.strong_count() > 1);
        let new_size = self.map.len();
        debug!(target: "ir::term::gc", "{} of {} types collected", old_size - new_size, old_size);
    }
}

lazy_static! {
    static ref TERMS: RwLock<TermTable> = RwLock::new(TermTable {
        map: FxHashMap::default(),
        count: 0,
        last_len: 0,
    });
}

// Tests are executed concurrently, meaning that terms might be collected
// in one thread, breaking constant folding or type checking running in a
// different thread. To fix this, we add a lock that the collector takes
// read-write, and cfolding / type-checking takes read-only.
//
// Deadlock analysis:
//      cfold takes FOLD_CACHE(w) -> TERMS(w)
//      type checking takes TERM_TYPES(w)
//      garbage collector takes one lock at a time
//
// The following locking priority MUST be observed:
//
// COLLECT -> FOLD_CACHE -> TERMS -> TERM_TYPES
lazy_static! {
    pub(super) static ref COLLECT: RwLock<()> = RwLock::new(());
}

fn mk(elm: TermData) -> Term {
    let mut slf = TERMS.write().unwrap();
    slf.mk(elm)
}

/// Scans the term database and the type database and removes dead terms and types.
pub fn garbage_collect() {
    // Don't garbage collect while panicking.
    // this function may be called from Drop implementations, which are called
    // when a thread is unwinding due to a panic. When that happens, RwLocks are
    // poisoned, which would cause a panic-in-panic, no bueno.
    if std::thread::panicking() {
        log::warn!("Not garbage collecting because we are currently panicking.");
        return;
    }

    // lock the collector before locking anything else
    let _lock = COLLECT.write().unwrap();
    collect_terms();
    collect_types();
    super::opt::cfold::collect();
}

const LEN_THRESH_NUM: usize = 8;
const LEN_THRESH_DEN: usize = 1;
const LEN_DECAY_NUM: usize = 15;
const LEN_DECAY_DEN: usize = 16;
/// Scan term and type databases only if they've grown in size since last scan
pub fn maybe_garbage_collect() -> bool {
    //// Don't garbage collect while panicking.
    //// NOTE This function probably shouldn't be called from Drop impls, but let's be safe anyway.
    //if std::thread::panicking() {
    //    log::warn!("Not garbage collecting because we are currently panicking.");
    //    return false;
    //}

    //// lock the collector before locking anything else
    //let _lock = COLLECT.write().unwrap();
    //let mut ran = false;
    //{
    //    let mut term_table = TERMS.write().unwrap();
    //    if term_table.should_collect() {
    //        term_table.collect();
    //        ran = true;
    //    }
    //} // TERMS lock goes out of scope here
    //if ran {
    //    collect_types();
    //    super::opt::cfold::collect();
    //}
    //ran
    return false;
}

fn collect_terms() {
    TERMS.write().unwrap().collect();
}

fn collect_types() {
    ty::TERM_TYPES.write().unwrap().collect();
}

impl TermData {
    /// Get the underlying boolean constant, if possible.
    pub fn as_bool_opt(&self) -> Option<bool> {
        if let Op::Const(Value::Bool(b)) = &self.op {
            Some(*b)
        } else {
            None
        }
    }
    /// Get the underlying bit-vector constant, if possible.
    pub fn as_bv_opt(&self) -> Option<&BitVector> {
        if let Op::Const(Value::BitVector(b)) = &self.op {
            Some(b)
        } else {
            None
        }
    }
    /// Get the underlying prime field constant, if possible.
    pub fn as_pf_opt(&self) -> Option<&FieldV> {
        if let Op::Const(Value::Field(b)) = &self.op {
            Some(b)
        } else {
            None
        }
    }

    /// Get the underlying tuple constant, if possible.
    pub fn as_tuple_opt(&self) -> Option<&[Value]> {
        if let Op::Const(Value::Tuple(t)) = &self.op {
            Some(t)
        } else {
            None
        }
    }

    /// Get the underlying array constant, if possible.
    pub fn as_array_opt(&self) -> Option<&Array> {
        if let Op::Const(Value::Array(a)) = &self.op {
            Some(a)
        } else {
            None
        }
    }

    /// Get the underlying constant value, if possible.
    pub fn as_value_opt(&self) -> Option<&Value> {
        if let Op::Const(v) = &self.op {
            Some(v)
        } else {
            None
        }
    }

    /// Is this a variable?
    pub fn is_var(&self) -> bool {
        matches!(&self.op, Op::Var(..))
    }

    /// Is this a value
    pub fn is_const(&self) -> bool {
        matches!(&self.op, Op::Const(..))
    }
}

impl Value {
    /// Compute the sort of this value
    pub fn sort(&self) -> Sort {
        match &self {
            Value::Bool(_) => Sort::Bool,
            Value::Field(f) => Sort::Field(f.ty()),
            Value::Int(_) => Sort::Int,
            Value::F64(_) => Sort::F64,
            Value::F32(_) => Sort::F32,
            Value::BitVector(b) => Sort::BitVector(b.width()),
            Value::Array(Array {
                key_sort,
                default,
                size,
                ..
            }) => Sort::Array(Box::new(key_sort.clone()), Box::new(default.sort()), *size),
            Value::Tuple(v) => Sort::Tuple(v.iter().map(Value::sort).collect()),
        }
    }
    #[track_caller]
    /// Get the underlying boolean constant, or panic!
    pub fn as_bool(&self) -> bool {
        if let Value::Bool(b) = self {
            *b
        } else {
            panic!("Not a bool: {}", self)
        }
    }
    #[track_caller]
    /// Get the underlying bit-vector constant, or panic!
    pub fn as_bv(&self) -> &BitVector {
        if let Value::BitVector(b) = self {
            b
        } else {
            panic!("Not a bit-vec: {}", self)
        }
    }
    #[track_caller]
    /// Get the underlying integer constant, or panic!
    pub fn as_int(&self) -> &Integer {
        if let Value::Int(b) = self {
            b
        } else {
            panic!("Not an int: {}", self)
        }
    }
    #[track_caller]
    /// Get the underlying prime field constant, if possible.
    pub fn as_pf(&self) -> &FieldV {
        if let Value::Field(b) = self {
            b
        } else {
            panic!("Not a field-elem: {}", self)
        }
    }
    #[track_caller]
    /// Get the underlying tuple's constituent values, if possible.
    pub fn as_tuple(&self) -> &[Value] {
        if let Value::Tuple(b) = self {
            b
        } else {
            panic!("Not a tuple: {}", self)
        }
    }

    #[track_caller]
    /// Unwrap the constituent value of this array, panicking otherwise.
    pub fn as_array(&self) -> &Array {
        if let Value::Array(w) = self {
            w
        } else {
            panic!("{} is not an aray", self)
        }
    }

    /// Get the underlying boolean constant, if possible.
    pub fn as_bool_opt(&self) -> Option<bool> {
        if let Value::Bool(b) = self {
            Some(*b)
        } else {
            None
        }
    }
    /// Get the underlying bit-vector constant, if possible.
    pub fn as_bv_opt(&self) -> Option<&BitVector> {
        if let Value::BitVector(b) = self {
            Some(b)
        } else {
            None
        }
    }

    /// Convert this value into a usize if possible
    pub fn as_usize(&self) -> Option<usize> {
        match &self {
            Value::Bool(b) => Some(*b as usize),
            Value::Field(f) => f.i().to_usize(),
            Value::Int(i) => i.to_usize(),
            Value::BitVector(b) => b.uint().to_usize(),
            _ => None,
        }
    }
}

/// Recursively the term `t`, using variable values in `h` and storing intermediate evaluations in
/// the cache `vs`.
pub fn eval_cached<'a>(
    t: &Term,
    h: &FxHashMap<String, Value>,
    vs: &'a mut TermMap<Value>,
) -> &'a Value {
    // the custom traversal (rather than [PostOrderIter]) allows us to break early based on the cache
    // (children pushed, term)
    let mut stack = vec![(false, t.clone())];
    while let Some((children_pushed, node)) = stack.pop() {
        if vs.contains_key(&node) {
            continue;
        }
        if children_pushed {
            eval_value(vs, h, node);
        } else {
            stack.push((true, node.clone()));
            for c in &node.cs {
                // vs doubles as our visited set.
                if !vs.contains_key(c) {
                    stack.push((false, c.clone()));
                }
            }
        }
    }
    vs.get(t).unwrap()
}

pub fn eval_cached_log<'a>(
    t: &Term,
    h: &FxHashMap<String, Value>,
    vs: &'a mut TermMap<Value>,
) -> &'a Value {
    println!("LOGGING");
    let start_cached = std::time::Instant::now();
    let mut pop = std::time::Duration::new(0, 0);
    let mut cont = std::time::Duration::new(0, 0);
    let mut push = std::time::Duration::new(0, 0);
    let mut children = std::time::Duration::new(0, 0);
    let mut eval = std::time::Duration::new(0, 0);
    // the custom traversal (rather than [PostOrderIter]) allows us to break early based on the cache
    // (children pushed, term)
    let mut max_stack = 0;
    let mut iters = 0;
    let mut stack = vec![(false, t.clone())];
    let mut time_map = HashMap::new();
    while true {
        let contains_t = std::time::Instant::now();
        let test = stack.pop();
        pop += contains_t.elapsed();
        if let Some((children_pushed, node)) = test {
            max_stack = core::cmp::max(stack.len(), max_stack);
            iters += 1;
            let contains_t = std::time::Instant::now();
            if vs.contains_key(&node) {
                continue;
            }
            cont += contains_t.elapsed();
            if children_pushed {
                let contains_t = std::time::Instant::now();
                eval_value_log(vs, h, node, &mut time_map);
                eval += contains_t.elapsed();
            } else {
                let contains_t = std::time::Instant::now();
                stack.push((true, node.clone()));
                push += contains_t.elapsed();
                let contains_t = std::time::Instant::now();
                for c in &node.cs {
                    // vs doubles as our visited set.
                    if !vs.contains_key(c) {
                        stack.push((false, c.clone()));
                    }
                }
                children += contains_t.elapsed();
            }
        } else {
            break;
        }
    }
    println!("DONE: iters: {}", iters);
    println!("DONE: {:?}", start_cached.elapsed());
    println!("cont: {:?}", cont);
    println!("pop: {:?}", cont);
    println!("push: {:?}", push);
    println!("eval: {:?}", eval);
    println!("child: {:?}", children);
    println!("TIME MAP: {:?}", time_map);
    vs.get(t).unwrap()
}

/// Recursively evaluate the term `t`, using variable values in `h`.
pub fn eval(t: &Term, h: &FxHashMap<String, Value>) -> Value {
    let mut vs = TermMap::<Value>::new();
    eval_cached(t, h, &mut vs).clone()
}

/// Helper function for eval function. Handles a single term
fn eval_value(vs: &mut TermMap<Value>, h: &FxHashMap<String, Value>, c: Term) -> Value {
    let v = match &c.op {
        Op::Var(n, _) => h
            .get(n)
            .unwrap_or_else(|| panic!("Missing var: {} in {:?}", n, h))
            .clone(),
        Op::Eq => Value::Bool(vs.get(&c.cs[0]).unwrap() == vs.get(&c.cs[1]).unwrap()),
        Op::Not => Value::Bool(!vs.get(&c.cs[0]).unwrap().as_bool()),
        Op::Implies => {
            Value::Bool(!vs.get(&c.cs[0]).unwrap().as_bool() || vs.get(&c.cs[1]).unwrap().as_bool())
        }
        Op::BoolNaryOp(BoolNaryOp::Or) => {
            Value::Bool(c.cs.iter().any(|c| vs.get(c).unwrap().as_bool()))
        }
        Op::BoolNaryOp(BoolNaryOp::And) => {
            Value::Bool(c.cs.iter().all(|c| vs.get(c).unwrap().as_bool()))
        }
        Op::BoolNaryOp(BoolNaryOp::Xor) => Value::Bool(
            c.cs.iter()
                .map(|c| vs.get(c).unwrap().as_bool())
                .fold(false, std::ops::BitXor::bitxor),
        ),
        Op::BvBit(i) => Value::Bool(vs.get(&c.cs[0]).unwrap().as_bv().uint().get_bit(*i as u32)),
        Op::BoolMaj => {
            let c0 = vs.get(&c.cs[0]).unwrap().as_bool() as u8;
            let c1 = vs.get(&c.cs[1]).unwrap().as_bool() as u8;
            let c2 = vs.get(&c.cs[2]).unwrap().as_bool() as u8;
            Value::Bool(c0 + c1 + c2 > 1)
        }
        Op::BvConcat => Value::BitVector({
            let mut it = c.cs.iter().map(|c| vs.get(c).unwrap().as_bv().clone());
            let f = it.next().unwrap();
            it.fold(f, BitVector::concat)
        }),
        Op::BvExtract(h, l) => {
            Value::BitVector(vs.get(&c.cs[0]).unwrap().as_bv().clone().extract(*h, *l))
        }
        Op::Const(v) => v.clone(),
        Op::BvBinOp(o) => Value::BitVector({
            let a = vs.get(&c.cs[0]).unwrap().as_bv().clone();
            let b = vs.get(&c.cs[1]).unwrap().as_bv().clone();
            match o {
                BvBinOp::Udiv => a / &b,
                BvBinOp::Urem => a % &b,
                BvBinOp::Sub => a - b,
                BvBinOp::Ashr => a.ashr(&b),
                BvBinOp::Lshr => a.lshr(&b),
                BvBinOp::Shl => a << &b,
            }
        }),
        Op::BvUnOp(o) => Value::BitVector({
            let a = vs.get(&c.cs[0]).unwrap().as_bv().clone();
            match o {
                BvUnOp::Not => !a,
                BvUnOp::Neg => -a,
            }
        }),
        Op::BvNaryOp(o) => Value::BitVector({
            let mut xs = c.cs.iter().map(|c| vs.get(c).unwrap().as_bv().clone());
            let f = xs.next().unwrap();
            xs.fold(
                f,
                match o {
                    BvNaryOp::Add => std::ops::Add::add,
                    BvNaryOp::Mul => std::ops::Mul::mul,
                    BvNaryOp::Xor => std::ops::BitXor::bitxor,
                    BvNaryOp::Or => std::ops::BitOr::bitor,
                    BvNaryOp::And => std::ops::BitAnd::bitand,
                },
            )
        }),
        Op::BvSext(w) => Value::BitVector({
            let a = vs.get(&c.cs[0]).unwrap().as_bv().clone();
            let mask = ((Integer::from(1) << *w as u32) - 1)
                * Integer::from(a.uint().get_bit(a.width() as u32 - 1));
            BitVector::new(a.uint() | (mask << a.width() as u32), a.width() + w)
        }),
        Op::PfToBv(w) => Value::BitVector({
            let i = vs.get(&c.cs[0]).unwrap().as_pf().i();
            let m = Integer::from(1) << *w as u32;
            let i = i.div_rem_floor(m.clone()).1;
            assert!(i < m);
            BitVector::new(i, *w)
        }),
        Op::BvUext(w) => Value::BitVector({
            let a = vs.get(&c.cs[0]).unwrap().as_bv().clone();
            BitVector::new(a.uint().clone(), a.width() + w)
        }),
        Op::Ite => if vs.get(&c.cs[0]).unwrap().as_bool() {
            vs.get(&c.cs[1])
        } else {
            vs.get(&c.cs[2])
        }
        .unwrap()
        .clone(),
        Op::BvBinPred(o) => Value::Bool({
            let a = vs.get(&c.cs[0]).unwrap().as_bv();
            let b = vs.get(&c.cs[1]).unwrap().as_bv();
            match o {
                BvBinPred::Sge => a.as_sint() >= b.as_sint(),
                BvBinPred::Sgt => a.as_sint() > b.as_sint(),
                BvBinPred::Sle => a.as_sint() <= b.as_sint(),
                BvBinPred::Slt => a.as_sint() < b.as_sint(),
                BvBinPred::Uge => a.uint() >= b.uint(),
                BvBinPred::Ugt => a.uint() > b.uint(),
                BvBinPred::Ule => a.uint() <= b.uint(),
                BvBinPred::Ult => a.uint() < b.uint(),
            }
        }),
        Op::BoolToBv => Value::BitVector(BitVector::new(
            Integer::from(vs.get(&c.cs[0]).unwrap().as_bool()),
            1,
        )),
        Op::PfUnOp(o) => Value::Field({
            let a = vs.get(&c.cs[0]).unwrap().as_pf().clone();
            match o {
                PfUnOp::Recip => {
                    if a.is_zero() {
                        a.ty().zero()
                    } else {
                        a.recip()
                    }
                }
                PfUnOp::Neg => -a,
            }
        }),
        Op::PfNaryOp(o) => Value::Field({
            let mut xs = c.cs.iter().map(|c| vs.get(c).unwrap().as_pf().clone());
            let f = xs.next().unwrap();
            xs.fold(
                f,
                match o {
                    PfNaryOp::Add => std::ops::Add::add,
                    PfNaryOp::Mul => std::ops::Mul::mul,
                },
            )
        }),
        Op::IntBinPred(o) => Value::Bool({
            let a = vs.get(&c.cs[0]).unwrap().as_int();
            let b = vs.get(&c.cs[1]).unwrap().as_int();
            match o {
                IntBinPred::Ge => a >= b,
                IntBinPred::Gt => a > b,
                IntBinPred::Le => a <= b,
                IntBinPred::Lt => a < b,
            }
        }),
        Op::IntNaryOp(o) => Value::Int({
            let mut xs = c.cs.iter().map(|c| vs.get(c).unwrap().as_int().clone());
            let f = xs.next().unwrap();
            xs.fold(
                f,
                match o {
                    IntNaryOp::Add => std::ops::Add::add,
                    IntNaryOp::Mul => std::ops::Mul::mul,
                },
            )
        }),
        Op::UbvToPf(fty) => Value::Field(fty.new_v(vs.get(&c.cs[0]).unwrap().as_bv().uint())),
        // tuple
        Op::Tuple => Value::Tuple(c.cs.iter().map(|c| vs.get(c).unwrap().clone()).collect()),
        Op::Field(i) => {
            let t = vs.get(&c.cs[0]).unwrap().as_tuple();
            assert!(i < &t.len(), "{} out of bounds for {}", i, c.cs[0]);
            t[*i].clone()
        }
        Op::Update(i) => {
            let mut t = Vec::from(vs.get(&c.cs[0]).unwrap().as_tuple()).into_boxed_slice();
            assert!(i < &t.len(), "{} out of bounds for {}", i, c.cs[0]);
            let e = vs.get(&c.cs[1]).unwrap().clone();
            assert_eq!(t[*i].sort(), e.sort());
            t[*i] = e;
            Value::Tuple(t)
        }
        // array
        Op::Store => {
            let a = vs.get(&c.cs[0]).unwrap().as_array();
            let i = vs.get(&c.cs[1]).unwrap().clone();
            let v = vs.get(&c.cs[2]).unwrap().clone();
            Value::Array(a.clone().store(i, v))
        }
        Op::Select => {
            let a = vs.get(&c.cs[0]).unwrap().as_array();
            let i = vs.get(&c.cs[1]).unwrap();
            a.select(i)
        }
        Op::Map(op) => {
            let arg_cnt = c.cs.len();

            //  term_vecs[i] will store a vector of all the i-th index entries of the array arguments
            let mut term_vecs = vec![Vec::new(); vs.get(&c.cs[0]).unwrap().as_array().size];

            for i in 0..arg_cnt {
                let arr = vs.get(&c.cs[i]).unwrap().as_array();
                let iter = match check(&c.cs[i]) {
                    Sort::Array(k, _, s) => (*k).clone().elems_iter_values().take(s).enumerate(),
                    _ => panic!("Input type should be Array"),
                };
                for (j, jval) in iter {
                    term_vecs[j].push(leaf_term(Op::Const(arr.clone().select(&jval))))
                }
            }

            let mut res = match check(&c) {
                Sort::Array(k, v, n) => Array::default((*k).clone(), &v, n),
                _ => panic!("Output type of map should be array"),
            };

            let iter = match check(&c) {
                Sort::Array(k, _, s) => (*k).clone().elems_iter_values().take(s).enumerate(),
                _ => panic!("Input type should be Array"),
            };
            for (i, idxval) in iter {
                let t = term((**op).clone(), term_vecs[i].clone());
                let val = eval_value(vs, h, t);
                res.map.insert(idxval, val);
            }
            Value::Array(res)
        }
        Op::Rot(i) => {
            let a = vs.get(&c.cs[0]).unwrap().as_array();
            let iter = match check(&c.cs[0]) {
                Sort::Array(k, _, s) => (*k).clone().elems_iter_values().take(s).enumerate(),
                _ => panic!("Input type should be Array"),
            };
            let (mut res, len) = match check(&c.cs[0]) {
                Sort::Array(k, v, n) => (Array::default((*k).clone(), &v, n), n),
                _ => panic!("Output type of rot should be Array"),
            };

            // calculate new rotation amount
            let rot = *i % len;
            for (idx, idx_val) in iter {
                let w = idx_val.as_bv().width();
                let new_idx = Value::BitVector(BitVector::new(Integer::from((idx + rot) % len), w));
                let new_val = a.select(&idx_val);
                res.map.insert(new_idx, new_val);
            }
            Value::Array(res)
        }

        Op::NthSmallest(i) => {
            panic!("HI THERE");
            let mut xs: Vec<Value> = c.cs.iter().map(|c| vs.get(c).unwrap().clone()).collect();
            order_stat::kth(&mut xs, *i).clone()
        }

        Op::Sort => {
            let time = std::time::Instant::now();
            let a = vs.get(&c.cs[0]).unwrap().as_array();
            let mut vals = Vec::new();
            let iter = match check(&c) {
                Sort::Array(k, _, s) => (*k).clone().elems_iter_values().take(s).enumerate(),
                _ => panic!("Input type should be Array"),
            };
            for (i, i_val) in iter {
                vals.push(a.map.get(&i_val).unwrap_or(&a.default).clone());
            }
            vals.sort();

            assert!(!vals.is_empty());
            let default = a.default.clone();
            let size = vals.len();
            let map = a.key_sort.elems_iter_values().zip(vals).collect();
            Value::Array(Array::new(a.key_sort.clone(), default, map, size))
        }

        Op::Array(key, value) => {
            let vals: Vec<Value> = c.cs.iter().map(|c| vs.get(c).unwrap().clone()).collect();
            Value::Array(Array::from_vec(key.clone(), value.clone(), vals))
        }

        Op::Waksman => {
            use circ_waksman::{n_switches, Config};
            let a = vs.get(&c.cs[0]).unwrap().as_array().values();
            let len = a.len();
            let cfg = Config::for_sorting(a);
            let switch_bools = Vec::from_iter(cfg.switches().into_iter().map(Value::Bool));
            assert_eq!(switch_bools.len(), n_switches(len));
            Value::Tuple(switch_bools.into())
        }
        o => unimplemented!("eval: {:?}", o),
    };
    vs.insert(c.clone(), v.clone());
    debug!("Eval {}\nAs   {}", c, v);
    v
}

use std::collections::HashMap;
use std::time::Duration;
fn eval_value_log(
    vs: &mut TermMap<Value>,
    h: &FxHashMap<String, Value>,
    c: Term,
    time_map: &mut HashMap<String, Duration>,
) -> Value {
    let start = std::time::Instant::now();
    let v = match &c.op {
        Op::Var(n, _) => h
            .get(n)
            .unwrap_or_else(|| panic!("Missing var: {} in {:?}", n, h))
            .clone(),
        Op::Eq => Value::Bool(vs.get(&c.cs[0]).unwrap() == vs.get(&c.cs[1]).unwrap()),
        Op::Not => Value::Bool(!vs.get(&c.cs[0]).unwrap().as_bool()),
        Op::Implies => {
            Value::Bool(!vs.get(&c.cs[0]).unwrap().as_bool() || vs.get(&c.cs[1]).unwrap().as_bool())
        }
        Op::BoolNaryOp(BoolNaryOp::Or) => {
            Value::Bool(c.cs.iter().any(|c| vs.get(c).unwrap().as_bool()))
        }
        Op::BoolNaryOp(BoolNaryOp::And) => {
            Value::Bool(c.cs.iter().all(|c| vs.get(c).unwrap().as_bool()))
        }
        Op::BoolNaryOp(BoolNaryOp::Xor) => Value::Bool(
            c.cs.iter()
                .map(|c| vs.get(c).unwrap().as_bool())
                .fold(false, std::ops::BitXor::bitxor),
        ),
        Op::BvBit(i) => Value::Bool(vs.get(&c.cs[0]).unwrap().as_bv().uint().get_bit(*i as u32)),
        Op::BoolMaj => {
            let c0 = vs.get(&c.cs[0]).unwrap().as_bool() as u8;
            let c1 = vs.get(&c.cs[1]).unwrap().as_bool() as u8;
            let c2 = vs.get(&c.cs[2]).unwrap().as_bool() as u8;
            Value::Bool(c0 + c1 + c2 > 1)
        }
        Op::BvConcat => Value::BitVector({
            let mut it = c.cs.iter().map(|c| vs.get(c).unwrap().as_bv().clone());
            let f = it.next().unwrap();
            it.fold(f, BitVector::concat)
        }),
        Op::BvExtract(h, l) => {
            Value::BitVector(vs.get(&c.cs[0]).unwrap().as_bv().clone().extract(*h, *l))
        }
        Op::Const(v) => v.clone(),
        Op::BvBinOp(o) => Value::BitVector({
            let a = vs.get(&c.cs[0]).unwrap().as_bv().clone();
            let b = vs.get(&c.cs[1]).unwrap().as_bv().clone();
            match o {
                BvBinOp::Udiv => a / &b,
                BvBinOp::Urem => a % &b,
                BvBinOp::Sub => a - b,
                BvBinOp::Ashr => a.ashr(&b),
                BvBinOp::Lshr => a.lshr(&b),
                BvBinOp::Shl => a << &b,
            }
        }),
        Op::BvUnOp(o) => Value::BitVector({
            let a = vs.get(&c.cs[0]).unwrap().as_bv().clone();
            match o {
                BvUnOp::Not => !a,
                BvUnOp::Neg => -a,
            }
        }),
        Op::BvNaryOp(o) => Value::BitVector({
            let mut xs = c.cs.iter().map(|c| vs.get(c).unwrap().as_bv().clone());
            let f = xs.next().unwrap();
            xs.fold(
                f,
                match o {
                    BvNaryOp::Add => std::ops::Add::add,
                    BvNaryOp::Mul => std::ops::Mul::mul,
                    BvNaryOp::Xor => std::ops::BitXor::bitxor,
                    BvNaryOp::Or => std::ops::BitOr::bitor,
                    BvNaryOp::And => std::ops::BitAnd::bitand,
                },
            )
        }),
        Op::BvSext(w) => Value::BitVector({
            let a = vs.get(&c.cs[0]).unwrap().as_bv().clone();
            let mask = ((Integer::from(1) << *w as u32) - 1)
                * Integer::from(a.uint().get_bit(a.width() as u32 - 1));
            BitVector::new(a.uint() | (mask << a.width() as u32), a.width() + w)
        }),
        Op::PfToBv(w) => Value::BitVector({
            let i = vs.get(&c.cs[0]).unwrap().as_pf().i();
            let m = Integer::from(1) << *w as u32;
            let i = i.div_rem_floor(m.clone()).1;
            assert!(i < m);
            BitVector::new(i, *w)
        }),
        Op::BvUext(w) => Value::BitVector({
            let a = vs.get(&c.cs[0]).unwrap().as_bv().clone();
            BitVector::new(a.uint().clone(), a.width() + w)
        }),
        Op::Ite => if vs.get(&c.cs[0]).unwrap().as_bool() {
            vs.get(&c.cs[1])
        } else {
            vs.get(&c.cs[2])
        }
        .unwrap()
        .clone(),
        Op::BvBinPred(o) => Value::Bool({
            let a = vs.get(&c.cs[0]).unwrap().as_bv();
            let b = vs.get(&c.cs[1]).unwrap().as_bv();
            match o {
                BvBinPred::Sge => a.as_sint() >= b.as_sint(),
                BvBinPred::Sgt => a.as_sint() > b.as_sint(),
                BvBinPred::Sle => a.as_sint() <= b.as_sint(),
                BvBinPred::Slt => a.as_sint() < b.as_sint(),
                BvBinPred::Uge => a.uint() >= b.uint(),
                BvBinPred::Ugt => a.uint() > b.uint(),
                BvBinPred::Ule => a.uint() <= b.uint(),
                BvBinPred::Ult => a.uint() < b.uint(),
            }
        }),
        Op::BoolToBv => Value::BitVector(BitVector::new(
            Integer::from(vs.get(&c.cs[0]).unwrap().as_bool()),
            1,
        )),
        Op::PfUnOp(o) => Value::Field({
            let a = vs.get(&c.cs[0]).unwrap().as_pf().clone();
            match o {
                PfUnOp::Recip => {
                    if a.is_zero() {
                        a.ty().zero()
                    } else {
                        a.recip()
                    }
                }
                PfUnOp::Neg => -a,
            }
        }),
        Op::PfNaryOp(o) => Value::Field({
            let mut xs = c.cs.iter().map(|c| vs.get(c).unwrap().as_pf().clone());
            let f = xs.next().unwrap();
            xs.fold(
                f,
                match o {
                    PfNaryOp::Add => std::ops::Add::add,
                    PfNaryOp::Mul => std::ops::Mul::mul,
                },
            )
        }),
        Op::IntBinPred(o) => Value::Bool({
            let a = vs.get(&c.cs[0]).unwrap().as_int();
            let b = vs.get(&c.cs[1]).unwrap().as_int();
            match o {
                IntBinPred::Ge => a >= b,
                IntBinPred::Gt => a > b,
                IntBinPred::Le => a <= b,
                IntBinPred::Lt => a < b,
            }
        }),
        Op::IntNaryOp(o) => Value::Int({
            let mut xs = c.cs.iter().map(|c| vs.get(c).unwrap().as_int().clone());
            let f = xs.next().unwrap();
            xs.fold(
                f,
                match o {
                    IntNaryOp::Add => std::ops::Add::add,
                    IntNaryOp::Mul => std::ops::Mul::mul,
                },
            )
        }),
        Op::UbvToPf(fty) => Value::Field(fty.new_v(vs.get(&c.cs[0]).unwrap().as_bv().uint())),
        // tuple
        Op::Tuple => Value::Tuple(c.cs.iter().map(|c| vs.get(c).unwrap().clone()).collect()),
        Op::Field(i) => {
            let t = vs.get(&c.cs[0]).unwrap().as_tuple();
            assert!(i < &t.len(), "{} out of bounds for {}", i, c.cs[0]);
            t[*i].clone()
        }
        Op::Update(i) => {
            let mut t = Vec::from(vs.get(&c.cs[0]).unwrap().as_tuple()).into_boxed_slice();
            assert!(i < &t.len(), "{} out of bounds for {}", i, c.cs[0]);
            let e = vs.get(&c.cs[1]).unwrap().clone();
            assert_eq!(t[*i].sort(), e.sort());
            t[*i] = e;
            Value::Tuple(t)
        }
        // array
        Op::Store => {
            let a = vs.get(&c.cs[0]).unwrap().as_array().clone();
            let i = vs.get(&c.cs[1]).unwrap().clone();
            let v = vs.get(&c.cs[2]).unwrap().clone();
            Value::Array(a.store(i, v))
        }
        Op::Select => {
            let a = vs.get(&c.cs[0]).unwrap().as_array();
            let i = vs.get(&c.cs[1]).unwrap();
            a.select(i)
        }
        Op::Map(op) => {
            let arg_cnt = c.cs.len();

            //  term_vecs[i] will store a vector of all the i-th index entries of the array arguments
            let mut term_vecs = vec![Vec::new(); vs.get(&c.cs[0]).unwrap().as_array().size];

            for i in 0..arg_cnt {
                let arr = vs.get(&c.cs[i]).unwrap().as_array().clone();
                let iter = match check(&c.cs[i]) {
                    Sort::Array(k, _, s) => (*k).clone().elems_iter_values().take(s).enumerate(),
                    _ => panic!("Input type should be Array"),
                };
                for (j, jval) in iter {
                    term_vecs[j].push(leaf_term(Op::Const(arr.clone().select(&jval))))
                }
            }

            let mut res = match check(&c) {
                Sort::Array(k, v, n) => Array::default((*k).clone(), &v, n),
                _ => panic!("Output type of map should be array"),
            };

            let iter = match check(&c) {
                Sort::Array(k, _, s) => (*k).clone().elems_iter_values().take(s).enumerate(),
                _ => panic!("Input type should be Array"),
            };
            for (i, idxval) in iter {
                let t = term((**op).clone(), term_vecs[i].clone());
                let val = eval_value(vs, h, t);
                res.map.insert(idxval, val);
            }
            Value::Array(res)
        }
        Op::Rot(i) => {
            let a = vs.get(&c.cs[0]).unwrap().as_array().clone();
            let iter = match check(&c.cs[0]) {
                Sort::Array(k, _, s) => (*k).clone().elems_iter_values().take(s).enumerate(),
                _ => panic!("Input type should be Array"),
            };
            let (mut res, len) = match check(&c.cs[0]) {
                Sort::Array(k, v, n) => (Array::default((*k).clone(), &v, n), n),
                _ => panic!("Output type of rot should be Array"),
            };

            // calculate new rotation amount
            let rot = *i % len;
            for (idx, idx_val) in iter {
                let w = idx_val.as_bv().width();
                let new_idx = Value::BitVector(BitVector::new(Integer::from((idx + rot) % len), w));
                let new_val = a.select(&idx_val);
                res.map.insert(new_idx, new_val);
            }
            Value::Array(res)
        }

        Op::NthSmallest(i) => {
            panic!("HI THERE");
            let mut xs: Vec<Value> = c.cs.iter().map(|c| vs.get(c).unwrap().clone()).collect();
            order_stat::kth(&mut xs, *i).clone()
        }

        Op::Sort => {
            let time = std::time::Instant::now();
            let a = vs.get(&c.cs[0]).unwrap().as_array().clone();
            let mut vals = Vec::new();
            let iter = match check(&c) {
                Sort::Array(k, _, s) => (*k).clone().elems_iter_values().take(s).enumerate(),
                _ => panic!("Input type should be Array"),
            };
            for (i, i_val) in iter {
                vals.push(a.map.get(&i_val).unwrap_or(&a.default).clone());
            }
            vals.sort();

            assert!(!vals.is_empty());
            let default = a.default;
            let size = vals.len();
            let map = a.key_sort.elems_iter_values().zip(vals).collect();
            Value::Array(Array::new(a.key_sort, default.clone(), map, size))
        }

        Op::Array(key, value) => {
            let vals: Vec<Value> = c.cs.iter().map(|c| vs.get(c).unwrap().clone()).collect();
            Value::Array(Array::from_vec(key.clone(), value.clone(), vals))
        }
        o => unimplemented!("eval: {:?}", o),
    };
    let elapsed = start.elapsed();
    let start = std::time::Instant::now();
    vs.insert(c.clone(), v.clone());
    let elapsed2 = start.elapsed();
    debug!("Eval {}\nAs   {}", c, v);
    let string = match c.op {
        Op::Var(_, _) => "VAR".to_owned(),
        Op::Field(_) => "FIELD".to_owned(),
        Op::Store => "STORE".to_owned(),
        Op::Select => "SELECT".to_owned(),
        _ => "OTHER".to_owned(),
    };
    time_map
        .entry(string)
        .and_modify(|v| *v += elapsed)
        .or_insert(elapsed);
    time_map
        .entry("CLONE".to_owned())
        .and_modify(|v| *v += elapsed2)
        .or_insert(elapsed2);
    v
}

/// Make an array from a sequence of terms.
///
/// Requires
///
/// * a key sort, as all arrays do. This sort must be iterable (i.e., bool, int, bit-vector, or field).
/// * a value sort, for the array's default
pub fn make_array(key_sort: Sort, value_sort: Sort, i: Vec<Term>) -> Term {
    let d = Sort::Array(Box::new(key_sort.clone()), Box::new(value_sort), i.len()).default_term();
    i.into_iter()
        .zip(key_sort.elems_iter())
        .fold(d, |arr, (val, idx)| term(Op::Store, vec![arr, idx, val]))
}

/// Make a term with no arguments, just an operator.
pub fn leaf_term(op: Op) -> Term {
    term(op, Vec::new())
}

/// Make a term with arguments.
#[track_caller]
pub fn term(op: Op, cs: Vec<Term>) -> Term {
    if let Op::Field(227) = op {
        match cs[0].op {
            Op::Array(..) => panic!("FOUND IT! cs: {:?}", cs),
            _ => {}
        }
    }
    #[cfg_attr(not(debug_assertions), allow(clippy::let_and_return))]
    let t = mk(TermData { op, cs });
    #[cfg(debug_assertions)]
    check_rec(&t);
    t
}

/// Make a prime-field constant term.
pub fn pf_lit(elem: FieldV) -> Term {
    leaf_term(Op::Const(Value::Field(elem)))
}

/// Make a bit-vector constant term.
pub fn bv_lit<T>(uint: T, width: usize) -> Term
where
    Integer: From<T>,
{
    leaf_term(Op::Const(Value::BitVector(BitVector::new(
        uint.into(),
        width,
    ))))
}

/// Make a bit-vector constant term.
pub fn bool_lit(b: bool) -> Term {
    leaf_term(Op::Const(Value::Bool(b)))
}

#[macro_export]
/// Make a term.
///
/// Syntax:
///
///    * without children: `term![OP]`
///    * with children: `term![OP; ARG0, ARG1, ... ]`
///       * Note the semi-colon
macro_rules! term {
    ($x:expr) => {
        leaf_term($x)
    };
    ($x:expr; $($y:expr),+) => {
        term($x, vec![$($y),+])
    };
}

#[macro_export]
/// Make a term, with clones.
///
/// Syntax:
///
///    * without children: `term![OP]`
///    * with children: `term![OP; ARG0, ARG1, ... ]`
///       * Note the semi-colon
macro_rules! term_c {
    ($x:expr; $($y:expr),+) => {
        {
            let mut args = Vec::new();
            #[allow(clippy::vec_init_then_push)]
            {
                $(
                    args.push(($y).clone());
                )+
            }
            term($x, args)
        }
    };
}

/// Map from terms
pub type TermMap<T> = hashconsing::coll::HConMap<Term, T>;
/// LRU cache of terms (like TermMap, but limited size)
pub type TermCache<T> = hashconsing::coll::WHConLru<Term, T>;
/// Set of terms
pub type TermSet = hashconsing::coll::HConSet<Term>;

// default LRU cache size
// this size avoids quadratic behavior for Falcon verification
pub(super) const TERM_CACHE_LIMIT: usize = 65536;

/// Iterator over descendents in child-first order.
pub struct PostOrderIter {
    // (cs stacked, term)
    stack: Vec<(bool, Term)>,
    visited: TermSet,
}

impl PostOrderIter {
    /// Make an iterator over the descendents of `root`.
    pub fn new(root: Term) -> Self {
        Self {
            stack: vec![(false, root)],
            visited: TermSet::new(),
        }
    }
}

impl std::iter::Iterator for PostOrderIter {
    type Item = Term;
    fn next(&mut self) -> Option<Term> {
        while let Some((children_pushed, t)) = self.stack.last() {
            if self.visited.contains(t) {
                self.stack.pop();
            } else if !children_pushed {
                self.stack.last_mut().unwrap().0 = true;
                let last = self.stack.last().unwrap().1.clone();
                self.stack
                    .extend(last.cs.iter().map(|c| (false, c.clone())));
            } else {
                break;
            }
        }
        self.stack.pop().map(|(_, t)| {
            self.visited.insert(t.clone());
            t
        })
    }
}

/// A party identifier
pub type PartyId = u8;

/// Epoch number for a particular input
pub type Epoch = u8;

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
/// An IR constraint system.
pub struct ComputationMetadata {
    /// A map from party names to numbers assigned to them.
    pub party_ids: FxHashMap<String, PartyId>,
    /// The next free id.
    pub next_party_id: PartyId,
    /// All inputs, including who knows them. If no visibility is set, the input is public.
    pub input_vis: FxHashMap<String, InputMetadata>,
    /// The inputs for the computation itself (not the precomputation).
    pub computation_inputs: Vec<String>,
}

/// An input to the computation
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InputMetadata {
    term: Term,
    visibility: Option<PartyId>,
    epoch: Epoch,
    random: bool,
}

impl InputMetadata {
    fn new(term: Term, visibility: Option<PartyId>, epoch: Epoch, random: bool) -> InputMetadata {
        InputMetadata {
            term,
            visibility,
            epoch,
            random,
        }
    }
}

impl ComputationMetadata {
    /// Add a new party to the computation, getting a [PartyId] for them.
    pub fn add_party(&mut self, name: String) -> PartyId {
        self.party_ids.insert(name, self.next_party_id);
        self.next_party_id += 1;
        self.next_party_id - 1
    }
    /// Add a new input to the computation, visible to `party`, or public if `party` is [None].
    pub fn new_input(
        &mut self,
        input_name: String,
        party: Option<PartyId>,
        epoch: Epoch,
        random: bool,
        sort: Sort,
    ) {
        let term = leaf_term(Op::Var(input_name.clone(), sort));
        debug_assert!(
            !self.input_vis.contains_key(&input_name)
                || self.input_vis.get(&input_name).unwrap().visibility == party,
            "Tried to create input {} (visibility {:?}), but it already existed (visibility {:?})",
            input_name,
            party,
            self.input_vis.get(&input_name).unwrap()
        );
        self.input_vis.insert(
            input_name.clone(),
            InputMetadata::new(term, party, epoch, random),
        );
        self.computation_inputs.push(input_name);
    }
    /// Returns None if the value is public. Otherwise, the unique party that knows it.
    pub fn get_input_visibility(&self, input_name: &str) -> Option<PartyId> {
        self.input_vis
            .get(input_name)
            .unwrap_or_else(|| {
                panic!(
                    "Missing input {} in inputs{:#?}",
                    input_name, self.input_vis
                )
            })
            .visibility
    }
    /// Returns the epoch number for the input.
    pub fn get_epoch(&self, input_name: &str) -> Epoch {
        self.input_vis
            .get(input_name)
            .unwrap_or_else(|| {
                panic!(
                    "Missing input {} in inputs{:#?}",
                    input_name, self.input_vis
                )
            })
            .epoch
    }
    /// Is this input public?
    pub fn is_input(&self, input_name: &str) -> bool {
        self.input_vis.contains_key(input_name)
    }
    /// Is this input public?
    pub fn is_input_public(&self, input_name: &str) -> bool {
        self.get_input_visibility(input_name).is_none()
    }
    /// What sort is this input?
    pub fn input_sort(&self, input_name: &str) -> Sort {
        check(&self.input_vis.get(input_name).unwrap().term)
    }
    /// Get all public inputs to the computation itself.
    ///
    /// Excludes pre-computation inputs
    pub fn public_input_names(&'_ self) -> impl Iterator<Item = &str> + '_ {
        self.input_vis.iter().filter_map(move |(name, party)| {
            if party.visibility.is_none() && self.computation_inputs.contains(name) {
                Some(name.as_str())
            } else {
                None
            }
        })
    }
    /// Get all random inputs to the computation itself.
    ///
    /// Excludes pre-computation inputs
    pub fn random_input_names<'a>(&'a self) -> impl Iterator<Item = &str> + 'a {
        self.input_vis.iter().filter_map(move |(name, party)| {
            if party.random && self.computation_inputs.contains(name) {
                Some(name.as_str())
            } else {
                None
            }
        })
    }
    /// Get all public inputs to the computation itself.
    ///
    /// Excludes pre-computation inputs.
    // I think the lint is just broken here.
    // TODO: submit a patch
    #[allow(clippy::needless_lifetimes)]
    pub fn public_inputs<'a>(&'a self) -> impl Iterator<Item = Term> + 'a {
        // TODO: check order?
        self.input_vis.iter().filter_map(move |(name, input)| {
            if input.visibility.is_none() && self.computation_inputs.contains(name) {
                Some(input.term.clone())
            } else {
                None
            }
        })
    }
    /// Get all the inputs visible to `party`.
    pub fn get_inputs_for_party(&self, party: Option<PartyId>) -> FxHashMap<String, u8> {
        self.input_vis
            .iter()
            .filter_map(|(name, input)| {
                if input.visibility.is_none() || input.visibility == party {
                    Some((name.clone(), input.epoch))
                } else {
                    None
                }
            })
            .collect()
    }

    /// get all inputs visible to `party` that can be computed in the given epoch.
    pub fn get_inputs_for_party_epoch(
        &self,
        party: Option<PartyId>,
        epoch: u8,
    ) -> FxHashSet<String> {
        self.input_vis
            .iter()
            .filter_map(|(name, input)| {
                if input.visibility.is_none() || input.visibility == party && input.epoch == epoch {
                    Some(name.clone())
                } else {
                    None
                }
            })
            .collect()
    }

    /// From a list of parties, a list of inputs, and a list of visibilities,
    /// create a [ComputationMetadata].
    pub fn from_parts(
        parties: Vec<String>,
        mut inputs: FxHashMap<String, Term>,
        visibilities: FxHashMap<String, String>,
    ) -> Self {
        let party_ids: FxHashMap<String, PartyId> = parties
            .into_iter()
            .enumerate()
            .map(|(i, n)| (n, i as u8))
            .collect();
        let next_party_id = party_ids.len() as u8;
        let computation_inputs: Vec<String> = inputs.keys().cloned().collect();
        let input_vis = computation_inputs
            .iter()
            .map(|i| {
                let vis = visibilities.get(i).map(|p| *party_ids.get(p).unwrap());
                let term = inputs.remove(i).unwrap();
                (i.clone(), InputMetadata::new(term, vis, 0, false))
            })
            .collect();
        ComputationMetadata {
            party_ids,
            next_party_id,
            input_vis,
            computation_inputs,
        }
    }

    /// Remove an input
    pub fn remove_var(&mut self, name: &str) {
        self.input_vis.remove(name);
        if let Some(pos) = self.computation_inputs.iter().position(|x| *x == name) {
            self.computation_inputs.remove(pos);
        }
    }
}

impl Display for ComputationMetadata {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "(metadata\n  (")?;
        for id in 0..self.next_party_id {
            let party = self.party_ids.iter().find(|(_, i)| **i == id).unwrap().0;
            write!(f, " {}", party)?;
        }
        write!(f, ")\n  (")?;
        for input in self.input_vis.keys() {
            let sort = self.input_sort(input);
            write!(f, " ({} {})", input, sort)?;
        }
        write!(f, ")\n  (")?;
        for (input, input_meta) in &self.input_vis {
            if let Some(id) = input_meta.visibility {
                let party = self.party_ids.iter().find(|(_, i)| **i == id).unwrap();
                write!(f, " ({} {} {})", input, party.0, input_meta.epoch)?;
            }
        }
        write!(f, ")\n)")
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
/// An IR computation.
pub struct Computation {
    /// The outputs of the computation.
    pub outputs: Vec<Term>,
    /// Metadata about the computation. I.e. who knows what inputs
    pub metadata: ComputationMetadata,
    /// Pre-computations
    pub precomputes: precomp::PreComp,
}

impl Computation {
    /// Create a new variable, `name: s`, where `val_fn` can be called to get the concrete value,
    /// and `public` indicates whether this variable is public in the constraint system.
    ///
    /// ## Arguments
    ///
    ///    * `name`: the name of the new variable
    ///    * `s`: its sort
    ///    * `party`: its visibility: who knows it initially
    ///    * `precompute`: a precomputation that can determine its value (optional). Note that the
    ///      precomputation may rely on information that some parties do not have. In this case,
    ///      those parties will have to provide a value for the variables directly.
    pub fn new_var(
        &mut self,
        name: &str,
        s: Sort,
        party: Option<PartyId>,
        epoch: Epoch,
        random: bool,
        precompute: Option<Term>,
    ) -> Term {
        self.new_var_epoched(name, s, party, epoch, random, precompute)
    }

    /// Create a new variable, `name: s`, where `val_fn` can be called to get the concrete value,
    /// and `public` indicates whether this variable is public in the constraint system.
    ///
    /// ## Arguments
    ///
    ///    * `name`: the name of the new variable
    ///    * `s`: its sort
    ///    * `party`: its visibility: who knows it initially
    ///    * `epoch`: the epoch the input is chosen in
    ///    * `precompute`: a precomputation that can determine its value (optional). Note that the
    ///      precomputation may rely on information that some parties do not have. In this case,
    ///      those parties will have to provide a value for the variables directly.
    pub fn new_var_epoched(
        &mut self,
        name: &str,
        s: Sort,
        party: Option<PartyId>,
        epoch: Epoch,
        random: bool,
        precompute: Option<Term>,
    ) -> Term {
        debug!(
            "Var: {} : {} (visibility: {:?}, epoch: {:?})",
            name, s, epoch, party
        );
        self.metadata
            .new_input(name.to_owned(), party, epoch, random, s.clone());
        if let Some(p) = precompute {
            assert_eq!(&s, &check(&p));
            assert!(!random, "Cannot have a precompute on a random variable!");
            self.precomputes.add_output(name.to_owned(), p);
        }
        leaf_term(Op::Var(name.to_owned(), s))
    }

    /// Add a new input `new_input_var` to this computation,
    /// whose value is determined by `precomp`: a term over existing inputs.
    ///
    /// The visibility for `new_input_var` will be computed from the visibility of variables in
    /// `precomp`: there must be at most **one** non-public variable.
    ///
    /// The sort for `new_input_var` will be computed from `precomp`.
    pub fn extend_precomputation(&mut self, new_input_var: String, precomp: Term) {
        debug!("Precompute {}", new_input_var);
        let vis = {
            let mut input_visiblities: FxHashSet<Option<PartyId>> =
                extras::free_variables(precomp.clone())
                    .into_iter()
                    .map(|v| self.metadata.get_input_visibility(&v))
                    .collect();
            input_visiblities.remove(&None);
            match input_visiblities.len() {
                0 => None,
                1 => input_visiblities.into_iter().next().unwrap(),
                _ => panic!("Precomputation for new var {} with term\n\t{}\ninvolves multiple input non-public visibilities:\n\t{:?}", new_input_var, precomp, input_visiblities),
            }
        };
        // TODO: Does this make sense?
        //       Can you ever have a precomputed value with an epoch that isn't 0?
        let epoch = {
            let input_epochs: FxHashSet<Epoch> = extras::free_variables(precomp.clone())
                .into_iter()
                .map(|v| self.metadata.get_epoch(&v))
                .collect();
            *input_epochs.iter().max().unwrap_or(&0)
        };
        let sort = check(&precomp);
        self.new_var(&new_input_var, sort, vis, epoch, false, Some(precomp));
    }

    /// Change the sort of a variables
    pub fn remove_var(&mut self, var: &str) {
        self.metadata.remove_var(var);
    }

    /// Assert `s` in the system.
    pub fn assert(&mut self, s: Term) {
        assert!(check(&s) == Sort::Bool);
        debug!("Assert: {}", &s.op);
        self.outputs.push(s);
    }

    /// Create a new system, which tracks values iff `values`.
    pub fn new() -> Self {
        Self {
            outputs: Vec::new(),
            metadata: ComputationMetadata::default(),
            precomputes: Default::default(),
        }
    }

    /// Get the outputs of the computation.
    ///
    /// For proof systems, these are the assertions that must hold.
    pub fn outputs(&self) -> &Vec<Term> {
        &self.outputs
    }

    /// How many total (unique) terms are there?
    pub fn terms(&self) -> usize {
        let mut terms = FxHashSet::<Term>::default();
        for a in &self.outputs {
            for s in PostOrderIter::new(a.clone()) {
                terms.insert(s);
            }
        }
        terms.len()
    }

    /// An iterator that visits each term in the computation, once.
    pub fn terms_postorder(&self) -> impl Iterator<Item = Term> {
        let mut terms: Vec<_> = PostOrderIter::new(term(Op::Tuple, self.outputs.clone())).collect();
        // drop the top-level tuple term.
        terms.pop();
        terms.into_iter()
    }

    pub fn terms_postorder_skip<'a, F: Fn(&Term) -> bool + 'a>(
        &self,
        f: &'a F,
    ) -> impl Iterator<Item = Term> + 'a {
        PostOrderSkipIter::new(term(Op::Tuple, self.outputs.clone()), f)
    }
}

impl Serialize for Computation {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let bytes = text::serialize_computation(self);
        serializer.serialize_str(&bytes)
    }
}

struct ComputationDeserVisitor;

impl<'de> Visitor<'de> for ComputationDeserVisitor {
    type Value = Computation;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "a string (that textually defines a term)")
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: std::error::Error,
    {
        Ok(text::parse_computation(v.as_bytes()))
    }
}

impl<'de> Deserialize<'de> for Computation {
    fn deserialize<D>(deserializer: D) -> Result<Computation, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_str(ComputationDeserVisitor)
    }
}

#[derive(Clone, Debug, Default)]
/// A map of IR computations.
pub struct Computations {
    /// A map of function name --> function computation
    pub comps: FxHashMap<String, Computation>,
}

impl Computations {
    /// Create new empty computations.
    pub fn new() -> Self {
        Self {
            comps: FxHashMap::default(),
        }
    }

    /// Get computation by name
    pub fn get(&self, name: &str) -> &Computation {
        match self.comps.get(name) {
            Some(c) => c,
            None => panic!("Unknown computation: {}", name),
        }
    }
}

#[cfg(test)]
pub mod test;
