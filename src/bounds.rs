//! Bounds, clock identifiers, and difference constraints.
//!
//! A [`Bound`] is a strict (`< c`) or non-strict (`<= c`) bound, or
//! [infinity](Bound::INFINITY) when no finite limit is imposed. Smaller
//! bounds are tighter.
//!
//! A [`Clock`] identifies any clock, including the fixed reference clock
//! [`Clock::ZERO`]; a [`Variable`] identifies only an actual clock and
//! is used for reset and free operations. A [`Constraint`] bounds the
//! difference between two clocks. The [`constraint!`](crate::constraint)
//! macro provides concise notation for common clock guards.

// Source-level implementation and proof notes (not part of public API Rustdoc).
// Packed `i32` bounds, clock identifiers and difference constraints.
//
// `Le(c)` means a non-strict upper bound (`<= c`), `Lt(c)` means a
// strict upper bound (`< c`), and `∞` imposes no restriction.
//
// # Encoding
//
// A [`Bound`] is one `i32` in an order-preserving encoding
// (see the encoding below):
//
// | bound | code |
// |---|---|
// | `Lt(c)` | `2c` |
// | `Le(c)` | `2c + 1` |
// | `∞` | `0x7FFF_FFFE` (the reserved infinity value) |
//
// with `c ∈ [MIN_CONSTANT, MAX_CONSTANT] = [−(2²⁹−1), 2²⁹−1]`. Valid finite
// codes therefore lie in `[−2³⁰+2, 2³⁰−1]`. Every other bit pattern except
// the infinity code is unconstructible (a type invariant, checked by the
// proofs). Comparing codes as integers is the tightness order.
//
// # Headroom
//
// Finite codes satisfy `|code| < 2³⁰`, so the sum of two codes lies strictly
// inside `(−2³¹, 2³¹)` and packed addition `a + b − ((a | b) & 1)` cannot
// overflow `i32`. [`Bound::checked_add`] computes it in `i32` and then checks
// that the result is a valid code. An out-of-range finite sum is
// [`Error::Range`], never `∞`.
//
// # Verification
//
// The functions below are the verified ones. Their contracts are stated
// against the logical model [`BoundModel`] and are proved by Creusot v0.14.0
// (`verification/scripts/prove-crate.sh`). Contracts and lemmas erase in
// ordinary builds. See `verification/PROOF_STATUS.md`.

use crate::dbm::MAX_VARIABLES;
use crate::error::Error;
use creusot_std::{
    invariant::{Invariant, inv},
    logic::real::Real,
    prelude::{Clone, PartialEq, *},
};

/// Largest representable finite constant: `2²⁹ − 1`.
// Literal values (not `(1 << 29) - 1` etc.): Creusot keeps computed
// constants opaque, so the proofs need them spelled out. Unit tests below
// check them against their defining expressions.
pub const MAX_CONSTANT: i32 = 0x1FFF_FFFF;
/// Smallest representable finite constant: `−MAX_CONSTANT` (symmetric, so
/// negating a representable constant is always representable).
pub const MIN_CONSTANT: i32 = -0x1FFF_FFFF;

/// The reserved encoding for infinity.
const INF: i32 = 0x7FFF_FFFE;
/// Smallest valid code, `Lt(MIN_CONSTANT)`.
const MIN_CODE: i32 = -0x3FFF_FFFE;
/// Largest valid finite code, `Le(MAX_CONSTANT)`.
const MAX_CODE: i32 = 0x3FFF_FFFF;

/// Logical (ghost) model of a bound: `x − y < c`, `x − y ≤ c`, or no
/// constraint. Used only in specifications.
pub enum BoundModel {
    /// `< c`
    Lt(Int),
    /// `≤ c`
    Le(Int),
    /// `< ∞`
    Inf,
}

impl BoundModel {
    /// Whether a finite constant is representable.
    #[logic(open)]
    pub fn in_range(c: Int) -> bool {
        pearlite! { MIN_CONSTANT@ <= c && c <= MAX_CONSTANT@ }
    }

    /// Tightness order `≼`: `self` is at least as tight as `other`.
    #[logic(open)]
    pub fn le(self, other: BoundModel) -> bool {
        match (self, other) {
            (_, BoundModel::Inf) => true,
            (BoundModel::Inf, _) => false,
            (BoundModel::Lt(a), BoundModel::Lt(b)) => a <= b,
            (BoundModel::Lt(a), BoundModel::Le(b)) => a <= b,
            (BoundModel::Le(a), BoundModel::Lt(b)) => a < b,
            (BoundModel::Le(a), BoundModel::Le(b)) => a <= b,
        }
    }

    /// Bound addition: constants add, the result is
    /// strict iff a summand is strict, and `∞` absorbs.
    #[logic(open)]
    pub fn add(self, other: BoundModel) -> BoundModel {
        match (self, other) {
            (BoundModel::Inf, _) | (_, BoundModel::Inf) => BoundModel::Inf,
            (BoundModel::Le(a), BoundModel::Le(b)) => BoundModel::Le(a + b),
            (BoundModel::Lt(a), BoundModel::Lt(b))
            | (BoundModel::Lt(a), BoundModel::Le(b))
            | (BoundModel::Le(a), BoundModel::Lt(b)) => BoundModel::Lt(a + b),
        }
    }

    /// The sum of two bounds is representable (trivially so if infinite).
    #[logic(open)]
    pub fn add_in_range(self, other: BoundModel) -> bool {
        match (self, other) {
            (BoundModel::Inf, _) | (_, BoundModel::Inf) => true,
            (BoundModel::Lt(a) | BoundModel::Le(a), BoundModel::Lt(b) | BoundModel::Le(b)) => {
                BoundModel::in_range(a + b)
            }
        }
    }

    /// Negation of finite bounds: `Le c ↦ Lt (−c)`,
    /// `Lt c ↦ Le (−c)`. Meaningful for finite bounds only.
    #[logic(open)]
    pub fn neg(self) -> BoundModel {
        match self {
            BoundModel::Lt(c) => BoundModel::Le(-c),
            BoundModel::Le(c) => BoundModel::Lt(-c),
            BoundModel::Inf => BoundModel::Inf,
        }
    }

    /// The constant of a finite bound is representable.
    #[logic(open)]
    pub fn representable(self) -> bool {
        match self {
            BoundModel::Lt(c) | BoundModel::Le(c) => BoundModel::in_range(c),
            BoundModel::Inf => true,
        }
    }
}

/// `d` satisfies `b`: the constraint `x − y ⋈ c` holds
/// when `x − y = d`. Differences are real numbers, never integers.
#[logic(open)]
pub fn sat(b: BoundModel, d: Real) -> bool {
    match b {
        BoundModel::Lt(c) => d < Real::from_int(c),
        BoundModel::Le(c) => d <= Real::from_int(c),
        BoundModel::Inf => true,
    }
}

/// Soundness of addition over the reals.
#[logic]
#[requires(sat(a, x) && sat(b, y))]
#[ensures(sat(a.add(b), x + y))]
pub fn add_sound(a: BoundModel, b: BoundModel, x: Real, y: Real) {}

/// The tightness order implies inclusion of real solution sets.
#[logic]
#[requires(a.le(b))]
#[requires(sat(a, d))]
#[ensures(sat(b, d))]
pub fn le_sound(a: BoundModel, b: BoundModel, d: Real) {}

/// Inclusion of real solution sets implies the tightness order.
#[logic]
#[requires(forall<d: Real> sat(a, d) ==> sat(b, d))]
#[ensures(a.le(b))]
pub fn le_complete(a: BoundModel, b: BoundModel) {
    pearlite! {
        match a {
            BoundModel::Lt(ca) => {
                let w = Real::from_int(ca) - half();
                proof_assert!(sat(a, w));
                proof_assert!(sat(b, w));
            }
            BoundModel::Le(ca) => {
                proof_assert!(sat(a, Real::from_int(ca)));
                proof_assert!(sat(b, Real::from_int(ca)));
            }
            BoundModel::Inf => match b {
                BoundModel::Lt(cb) | BoundModel::Le(cb) => {
                    proof_assert!(sat(a, Real::from_int(cb + 1)));
                    proof_assert!(sat(b, Real::from_int(cb + 1)));
                }
                BoundModel::Inf => {}
            },
        }
    }
}

#[logic(open)]
fn half() -> Real {
    Real::from_int(1) / Real::from_int(2)
}

/// Real (not integer) semantics: `< c+1` and `≤ c` differ at `c + 1/2`.
#[logic]
#[ensures(sat(BoundModel::Lt(c + 1), Real::from_int(c) + half()))]
#[ensures(!sat(BoundModel::Le(c), Real::from_int(c) + half()))]
pub fn strict_is_not_integer(c: Int) {}

/// Negation is the complement:
/// `¬sat(r, b) ⟺ sat(−r, neg b)` for finite `b`.
#[logic]
#[requires(b != BoundModel::Inf)]
#[ensures(forall<r: Real> !sat(b, r) == sat(b.neg(), -r))]
pub fn neg_complement(b: BoundModel) {}

/// The constant range is symmetric, so negating a representable constant
/// (e.g. to write the lower-bound guard `x ≥ c` as `0 − x ≤ −c`) is
/// representable, and so is negating a representable finite bound.
#[logic]
#[requires(BoundModel::in_range(c))]
#[ensures(BoundModel::in_range(-c))]
#[ensures(BoundModel::Lt(c).neg().representable() && BoundModel::Le(c).neg().representable())]
pub fn neg_in_range(c: Int) {}

/// `Lt c ≺ Le c ≺ Lt (c+1) ≺ ∞`.
#[logic]
#[ensures(BoundModel::Lt(c).le(BoundModel::Le(c)) && !BoundModel::Le(c).le(BoundModel::Lt(c)))]
#[ensures(BoundModel::Le(c).le(BoundModel::Lt(c + 1)) && !BoundModel::Lt(c + 1).le(BoundModel::Le(c)))]
#[ensures(BoundModel::Le(c).le(BoundModel::Inf) && !BoundModel::Inf.le(BoundModel::Le(c)))]
pub fn tightness_chain(c: Int) {}

// ----- algebra of `(𝔹, ≼, +, Le 0)` used by the closure proof -----
//
// These are the algebraic facts needed by the closure proof,
// restated and proved for `BoundModel`.

/// `≼` is reflexive and transitive.
#[logic]
#[ensures(a.le(a))]
#[ensures(a.le(b) && b.le(c) ==> a.le(c))]
pub fn le_trans(a: BoundModel, b: BoundModel, c: BoundModel) {}

/// `≼` is total and antisymmetric.
#[logic]
#[ensures(a.le(b) || b.le(a))]
#[ensures(a.le(b) && b.le(a) ==> a == b)]
pub fn le_total(a: BoundModel, b: BoundModel) {}

/// `+` is commutative and has unit `Le 0`; `∞` absorbs.
#[logic]
#[ensures(a.add(b) == b.add(a))]
#[ensures(a.add(BoundModel::Le(0)) == a)]
#[ensures(a.add(BoundModel::Inf) == BoundModel::Inf)]
pub fn add_comm_unit(a: BoundModel, b: BoundModel) {}

/// `+` is associative.
#[logic]
#[ensures(a.add(b).add(c) == a.add(b.add(c)))]
pub fn add_assoc(a: BoundModel, b: BoundModel, c: BoundModel) {}

/// `+` is monotone in `≼` (in each argument).
#[logic]
#[requires(a.le(b))]
#[ensures(a.add(c).le(b.add(c)))]
#[ensures(c.add(a).le(c.add(b)))]
pub fn add_mono(a: BoundModel, b: BoundModel, c: BoundModel) {}

/// A bound strictly tighter than `Le 0` excludes the difference 0, e.g. the
/// strict-zero cycle `Lt 0`.
#[logic]
#[requires(!BoundModel::Le(0).le(b))]
#[ensures(!sat(b, Real::from_int(0)))]
pub fn below_le_zero_unsat(b: BoundModel) {}

/// `PartialOrd`/`Ord` on the single field, i.e. on the deep model (the packed
/// code or the clock index). Written out instead of derived because Creusot
/// needs the contract that refines the `Ord` trait specification.
macro_rules! ord_by_deep_model {
    ($t:ty) => {
        impl PartialOrd for $t {
            #[check(terminates)]
            #[ensures(result == (*self).deep_model().partial_cmp_log((*other).deep_model()))]
            fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
                Some(self.cmp(other))
            }
        }

        impl Ord for $t {
            #[check(terminates)]
            #[ensures(result == (*self).deep_model().cmp_log((*other).deep_model()))]
            fn cmp(&self, other: &Self) -> core::cmp::Ordering {
                self.0.cmp(&other.0)
            }
        }
    };
}

/// A strict bound `x - y < c`, a non-strict bound `x - y <= c`,
/// or infinity (no restriction on the difference).
///
/// Construct bounds with [`Bound::lt`], [`Bound::le`], or
/// [`Bound::INFINITY`].
/// The [`Ord`] implementation orders bounds by *tightness*: smaller bounds
/// exclude at least as many valuations.
///
/// # Example
///
/// ```
/// use clock_dbm::Bound;
/// # fn main() -> Result<(), clock_dbm::Error> {
/// assert!(Bound::lt(3)? < Bound::le(3)?);
/// assert_eq!(Bound::lt(2)?.checked_add(Bound::le(3)?)?, Bound::lt(5)?);
/// assert!(Bound::INFINITY.is_infinite());
/// # Ok(())
/// # }
/// ```
#[derive(Copy, PartialEq, Eq, Debug)]
// `Hash` is not translated by Creusot (std's `Hasher` has no specs); it is
// derived from the same field as `Eq`, so it is consistent with it.
#[cfg_attr(not(creusot), derive(Hash))]
pub struct Bound(i32);

ord_by_deep_model!(Bound);

// Written out instead of derived: the derived contract names the private
// field, which Creusot cannot resolve when another module clones a container
// of bounds (e.g. the `Box<[Bound]>` inside `Dbm`).
impl Clone for Bound {
    #[check(terminates)]
    #[ensures(result == *self)]
    fn clone(&self) -> Bound {
        *self
    }
}

impl Invariant for Bound {
    #[logic(open(self))]
    fn invariant(self) -> bool {
        pearlite! { (MIN_CODE@ <= self.0@ && self.0@ <= MAX_CODE@) || self.0 == INF }
    }
}

impl DeepModel for Bound {
    type DeepModelTy = Int;

    /// The packed code. The derived `Eq`/`Ord`/`Hash` work on this value.
    #[logic(open(self))]
    fn deep_model(self) -> Int {
        pearlite! { self.0@ }
    }
}

impl View for Bound {
    type ViewTy = BoundModel;

    #[logic(open(self))]
    fn view(self) -> BoundModel {
        pearlite! {
            if self.0 == INF {
                BoundModel::Inf
            } else if self.0@.rem_euclid(2) == 0 {
                BoundModel::Lt(self.0@.div_euclid(2))
            } else {
                BoundModel::Le(self.0@.div_euclid(2))
            }
        }
    }
}

/// Every bound denotes a representable model value.
#[logic]
#[requires(inv(b))]
#[ensures(b@.representable())]
pub fn view_representable(b: Bound) {}

/// B1: the encoding is injective, so equality of bounds (derived `Eq` on the
/// code) is equality of models.
#[logic]
#[requires(inv(a) && inv(b))]
#[ensures((a@ == b@) == (a.deep_model() == b.deep_model()))]
pub fn view_injective(a: Bound, b: Bound) {}

/// B2: comparing codes (the derived `Ord`) is the tightness order. With B1
/// this also gives B4: `Ord::min`/`max` are the model's `min`/`max`.
#[logic]
#[requires(inv(a) && inv(b))]
#[ensures((a.deep_model() <= b.deep_model()) == a@.le(b@))]
#[ensures((a.deep_model() < b.deep_model()) == (a@.le(b@) && a@ != b@))]
pub fn order_refines(a: Bound, b: Bound) {}

/// `(x | y) & 1` is 1 iff at least one of `x`, `y` is odd (a weak bound).
#[check(terminates)]
#[bitwise_proof]
#[ensures(result == 0i32 || result == 1i32)]
#[ensures((result == 1i32) == (x & 1i32 == 1i32 || y & 1i32 == 1i32))]
const fn weak_or(x: i32, y: i32) -> i32 {
    (x | y) & 1
}

/// Bit-level decomposition, proved by bitvector reasoning:
/// `x = (x >> 1) + (x >> 1) + (x & 1)` (in wrapping arithmetic), with the
/// ranges of both parts. This is the only place where bits meet arithmetic.
#[check(terminates)]
#[bitwise_proof]
#[ensures(x == (x >> 1i32) + (x >> 1i32) + (x & 1i32))]
#[ensures(x & 1i32 == 0i32 || x & 1i32 == 1i32)]
#[ensures(-0x4000_0000i32 <= (x >> 1i32) && (x >> 1i32) <= 0x3FFF_FFFFi32)]
#[allow(unused_variables)]
const fn bit_split(x: i32) {}

/// Integer-mode consequences of [`bit_split`]: the low bit is the Euclidean
/// remainder by 2 and the arithmetic shift is the Euclidean quotient.
#[check(terminates)]
#[ensures((x & 1i32)@ == x@.rem_euclid(2))]
#[ensures((x & 1i32 == 1i32) == (x@.rem_euclid(2) == 1))]
#[ensures(x & 1i32 == 0i32 || x & 1i32 == 1i32)]
#[ensures((x >> 1i32)@ == x@.div_euclid(2))]
const fn low_bit(x: i32) {
    bit_split(x);
}

impl Bound {
    /// A bound that places no restriction on a clock difference.
    #[ensures(Bound::INFINITY@ == BoundModel::Inf)]
    pub const INFINITY: Bound = Bound(INF);
    /// The non-strict bound `<= 0`, used on a canonical DBM's diagonal.
    #[ensures(Bound::LE_ZERO@ == BoundModel::Le(0))]
    pub const LE_ZERO: Bound = Bound(1);
    /// The strict bound `< 0`.
    #[ensures(Bound::LT_ZERO@ == BoundModel::Lt(0))]
    pub const LT_ZERO: Bound = Bound(0);

    /// Constructs the non-strict upper bound `<= c`.
    ///
    /// Returns [`Error::Range`] if `c` is outside the supported interval
    /// from [`MIN_CONSTANT`] to [`MAX_CONSTANT`].
    #[check(terminates)]
    #[ensures(match result {
        Ok(b) => BoundModel::in_range(c@) && b@ == BoundModel::Le(c@),
        Err(e) => !BoundModel::in_range(c@) && e == Error::Range,
    })]
    pub const fn le(c: i32) -> Result<Bound, Error> {
        if MIN_CONSTANT <= c && c <= MAX_CONSTANT {
            Ok(Bound(2 * c + 1))
        } else {
            Err(Error::Range)
        }
    }

    /// Constructs the strict upper bound `< c`.
    ///
    /// Returns [`Error::Range`] if `c` is outside the supported interval
    /// from [`MIN_CONSTANT`] to [`MAX_CONSTANT`].
    #[check(terminates)]
    #[ensures(match result {
        Ok(b) => BoundModel::in_range(c@) && b@ == BoundModel::Lt(c@),
        Err(e) => !BoundModel::in_range(c@) && e == Error::Range,
    })]
    pub const fn lt(c: i32) -> Result<Bound, Error> {
        if MIN_CONSTANT <= c && c <= MAX_CONSTANT {
            Ok(Bound(2 * c))
        } else {
            Err(Error::Range)
        }
    }

    /// Whether this is `∞`.
    #[check(terminates)]
    #[ensures(result == (self@ == BoundModel::Inf))]
    pub const fn is_infinite(self) -> bool {
        self.0 == INF
    }

    /// Returns whether the bound uses `<` rather than `<=`.
    ///
    /// An unrestricted (infinite) bound is not strict.
    #[check(terminates)]
    #[ensures(result == match self@ { BoundModel::Lt(_) => true, _ => false })]
    pub const fn is_strict(self) -> bool {
        low_bit(self.0);
        self.0 != INF && self.0 & 1 == 0
    }

    /// Returns the integer constant of a finite strict or non-strict
    /// bound, or `None` for an unrestricted (infinite) bound.
    #[check(terminates)]
    #[ensures(match self@ {
        BoundModel::Lt(c) | BoundModel::Le(c) => match result { Some(r) => r@ == c, None => false },
        BoundModel::Inf => result == None,
    })]
    pub const fn constant(self) -> Option<i32> {
        if self.0 == INF {
            None
        } else {
            low_bit(self.0);
            Some(self.0 >> 1)
        }
    }

    /// Adds two bounds, as when chaining clock-difference inequalities.
    ///
    /// The finite constants are added; the result is strict (`<`) if
    /// either operand is strict. If either bound is infinite, so is the
    /// sum. Returns [`Error::Range`] if a finite sum cannot be represented;
    /// it is never saturated to infinity.
    #[check(terminates)]
    #[ensures(match result {
        Ok(r) => self@.add_in_range(other@) && r@ == self@.add(other@),
        Err(e) => !self@.add_in_range(other@) && e == Error::Range,
    })]
    pub const fn checked_add(self, other: Bound) -> Result<Bound, Error> {
        if self.0 == INF || other.0 == INF {
            return Ok(Bound::INFINITY);
        }
        low_bit(self.0);
        low_bit(other.0);
        // Packed finite-bound addition. No overflow: both codes are in
        // [MIN_CODE, MAX_CODE] ⊂ (−2³⁰, 2³⁰).
        let r = (self.0 + other.0) - weak_or(self.0, other.0);
        if MIN_CODE <= r && r <= MAX_CODE {
            Ok(Bound(r))
        } else {
            Err(Error::Range)
        }
    }
}

// ----- adding a weak constant (temporal operations) -----

/// `b + via` for a finite **weak** `via = Le c`: the constant of a finite
/// `b` shifts by `c` and its strictness is kept (the code shifts by `2c`);
/// `∞` stays `∞`.
///
/// **Precondition:** the sum is representable (trivially so if `b = ∞`).
/// The reset of `ops::temporal` establishes it from the `Dbm` invariant
/// (`ops::temporal::proof::reset_representable`). No `i32` overflow: `b`
/// (with `∞` masked to 0) and `2c` both lie in `(−2³⁰, 2³⁰)`.
///
/// Branch-free, so that row loops vectorize. Proved: the result is
/// exactly `via + b` in the model.
#[check(terminates)]
#[requires(exists<c: Int> via@ == BoundModel::Le(c))]
#[requires(via@.add_in_range(b@))]
#[ensures(result@ == via@.add(b@))]
#[inline]
pub(crate) fn add_weak(b: Bound, via: Bound) -> Bound {
    snapshot!(enc_view(via));
    let fin = b.0 != INF;
    proof_assert!(fin ==> { enc_view(b); enc_range(via@.add(b@)); true });
    let sum = if fin { b.0 } else { 0 } + (via.0 - 1);
    proof_assert!(fin ==> sum@ == enc(via@.add(b@)));
    Bound(if fin { sum } else { INF })
}

/// `dst[l] := via + src[l]` for every `l` ([`add_weak`], whose precondition
/// must hold for every entry). Branch-free; it vectorizes.
#[check(terminates)]
#[requires(dst@.len() == src@.len())]
#[requires(exists<c: Int> via@ == BoundModel::Le(c))]
#[requires(forall<l: Int> 0 <= l && l < src@.len() ==> via@.add_in_range(src@[l]@))]
#[ensures((^dst)@.len() == dst@.len())]
#[ensures(forall<l: Int> 0 <= l && l < dst@.len() ==> (^dst)@[l]@ == via@.add(src@[l]@))]
#[inline]
pub(crate) fn add_weak_row(dst: &mut [Bound], via: Bound, src: &[Bound]) {
    let old = snapshot!(dst@);
    // `n ≤ src.len()` lets the compiler drop the bounds checks.
    let n = if dst.len() < src.len() {
        dst.len()
    } else {
        src.len()
    };
    let mut l: usize = 0;
    #[invariant(l@ <= n@ && n@ == old.len() && dst@.len() == old.len())]
    #[invariant(forall<k: Int> 0 <= k && k < l@ ==> dst@[k]@ == via@.add(src@[k]@))]
    #[variant(n@ - l@)]
    while l < n {
        dst[l] = add_weak(src[l], via);
        l += 1;
    }
}

// ----- row relaxation (incremental closure) -----

/// The packed code of a finite model bound, without range restriction:
/// `Lt c ↦ 2c`, `Le c ↦ 2c + 1`.
#[logic(open)]
pub fn enc(m: BoundModel) -> Int {
    match m {
        BoundModel::Lt(c) => 2 * c,
        BoundModel::Le(c) => 2 * c + 1,
        BoundModel::Inf => 0,
    }
}

/// `enc` is injective and order-preserving on finite bounds, and a valid
/// finite `Bound` stores exactly `enc` of its model.
#[logic]
#[requires(x != BoundModel::Inf && y != BoundModel::Inf)]
#[ensures(x.le(y) == (enc(x) <= enc(y)))]
#[ensures((enc(x) == enc(y)) == (x == y))]
pub fn enc_order(x: BoundModel, y: BoundModel) {}

/// A valid finite bound stores `enc` of its model.
#[logic]
#[requires(inv(b) && b@ != BoundModel::Inf)]
#[ensures(enc(b@) == b.deep_model())]
pub fn enc_view(b: Bound) {}

/// `b`'s model is representable iff its code lies in `[MIN_CODE, MAX_CODE]`.
#[logic]
#[requires(m != BoundModel::Inf)]
#[ensures(m.representable() == (MIN_CODE@ <= enc(m) && enc(m) <= MAX_CODE@))]
pub fn enc_range(m: BoundModel) {}

/// `via + s` is strictly tighter than `cur`: the entry must change.
#[logic(open)]
pub fn relax_needed(cur: BoundModel, via: BoundModel, s: BoundModel) -> bool {
    s != BoundModel::Inf && !cur.le(via.add(s))
}

/// One entry of [`relax_row`]: `new = via + s` if that sum is needed and
/// representable, otherwise `new = cur`.
#[logic(open)]
pub fn relax_entry(cur: BoundModel, via: BoundModel, s: BoundModel, new: BoundModel) -> bool {
    if relax_needed(cur, via, s) && via.add_in_range(s) {
        new == via.add(s)
    } else {
        new == cur
    }
}

/// `dst[l] := min(dst[l], via + src[l])` for every `l` with `src[l]`
/// finite (one row of a Floyd–Warshall-style relaxation through a finite
/// `via`). Returns `true` iff some needed sum is unrepresentable; that entry
/// is then left unchanged, so `dst` stays valid, and the caller reports
/// `Err(Range)`.
///
/// The loop is branch-free so that it vectorizes (as the incremental closure
/// does). An infinite `src[l]` is replaced by 0 before adding,
/// so no intermediate value can overflow `i32`. Unrepresentable needed sums
/// are *counted* in a `u32` rather than OR-ed into a `bool`: the loop-carried
/// `bool` reduction vectorized poorly and cost about 6 ns per tightening step
/// at `d = 5` (benchmark investigation).
#[check(terminates)]
#[requires(dst@.len() == src@.len())]
#[requires(dst@.len() <= u32::MAX@)]
#[requires(via@ != BoundModel::Inf)]
#[ensures((^dst)@.len() == dst@.len())]
#[ensures(forall<l: Int> 0 <= l && l < dst@.len() ==>
    relax_entry(dst@[l]@, via@, src@[l]@, (^dst)@[l]@))]
#[ensures(result ==> exists<l: Int> 0 <= l && l < dst@.len()
    && relax_needed(dst@[l]@, via@, src@[l]@) && !via@.add_in_range(src@[l]@))]
#[ensures(!result ==> forall<l: Int> 0 <= l && l < dst@.len() ==>
    !(relax_needed(dst@[l]@, via@, src@[l]@) && !via@.add_in_range(src@[l]@)))]
#[inline]
// Explicit, non-short-circuiting forms: they keep the loop branch-free (it
// must vectorize) and are what the proof reasons about.
#[allow(clippy::manual_range_contains, clippy::assign_op_pattern)]
pub(crate) fn relax_row(dst: &mut [Bound], via: Bound, src: &[Bound]) -> bool {
    let old = snapshot!(dst@);
    // `n ≤ src.len()` lets the compiler drop the bounds checks.
    let n = if dst.len() < src.len() {
        dst.len()
    } else {
        src.len()
    };
    let v = via.0;
    low_bit(v);
    snapshot!(enc_view(via));
    let mut bad: u32 = 0;
    let mut l: usize = 0;
    #[invariant(l@ <= n@ && n@ == old.len() && dst@.len() == old.len())]
    #[invariant(inv(dst))]
    #[invariant(forall<k: Int> 0 <= k && k < l@ ==>
        relax_entry(old[k]@, via@, src@[k]@, dst@[k]@))]
    #[invariant(forall<k: Int> l@ <= k && k < n@ ==> dst@[k] == old[k])]
    #[invariant(bad@ <= l@)]
    #[invariant((bad@ > 0) == exists<k: Int> 0 <= k && k < l@
        && relax_needed(old[k]@, via@, src@[k]@) && !via@.add_in_range(src@[k]@))]
    #[variant(n@ - l@)]
    while l < n {
        let s = src[l].0;
        let fin = s != INF;
        let s2 = if fin { s } else { 0 };
        low_bit(s2);
        let sum = (v + s2) - weak_or(v, s2);
        let cur = dst[l].0;
        let tighter = fin & (sum < cur);
        let ok = (MIN_CODE <= sum) & (sum <= MAX_CODE);
        proof_assert!(fin ==> {
            enc_view(src@[l@]); enc_view(dst@[l@]);
            enc_order(via@.add(src@[l@]@), dst@[l@]@);
            enc_range(via@.add(src@[l@]@));
            sum@ == enc(via@.add(src@[l@]@))
                && (tighter == relax_needed(dst@[l@]@, via@, src@[l@]@))
                && (ok == via@.add_in_range(src@[l@]@))
        });
        bad = bad + (tighter & !ok) as u32;
        let new = Bound(if tighter & ok { sum } else { cur });
        proof_assert!(tighter && ok ==> {
            enc_view(new); enc_order(new@, via@.add(src@[l@]@)); new@ == via@.add(src@[l@]@)
        });
        dst[l] = new;
        l += 1;
    }
    bad != 0
}

/// Any clock index, including the reference clock `x₀` (index 0).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(not(creusot), derive(Hash))]
pub struct Clock(u32);

ord_by_deep_model!(Clock);

impl Invariant for Clock {
    #[logic(open(self))]
    fn invariant(self) -> bool {
        pearlite! { self.0@ <= MAX_VARIABLES@ }
    }
}

impl DeepModel for Clock {
    type DeepModelTy = Int;

    #[logic(open(self))]
    fn deep_model(self) -> Int {
        pearlite! { self.0@ }
    }
}

impl View for Clock {
    type ViewTy = Int;

    /// The clock index.
    #[logic(open(self))]
    fn view(self) -> Int {
        pearlite! { self.0@ }
    }
}

impl Clock {
    /// The reference clock `x₀`.
    #[ensures(Clock::ZERO@ == 0)]
    pub const ZERO: Clock = Clock(0);

    /// The clock with this index. `None` if `index > MAX_VARIABLES`.
    #[check(terminates)]
    #[ensures(match result {
        Some(x) => index@ <= MAX_VARIABLES@ && x@ == index@,
        None => index@ > MAX_VARIABLES@,
    })]
    pub const fn new(index: usize) -> Option<Clock> {
        if index <= MAX_VARIABLES {
            Some(Clock(index as u32))
        } else {
            None
        }
    }

    /// The index (0 for the reference clock).
    #[check(terminates)]
    #[ensures(result@ == self@)]
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

/// An actual clock (index 1 or greater), used for resetting or freeing a clock.
///
/// Unlike [`Clock`], a `Variable` cannot represent the reference clock:
/// `Variable::new(0)` returns `None`. Convert a variable to a [`Clock`]
/// with `.into()` to use it in a [`Constraint`].
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(not(creusot), derive(Hash))]
pub struct Variable(u32);

ord_by_deep_model!(Variable);

impl Invariant for Variable {
    #[logic(open(self))]
    fn invariant(self) -> bool {
        pearlite! { 1 <= self.0@ && self.0@ <= MAX_VARIABLES@ }
    }
}

impl DeepModel for Variable {
    type DeepModelTy = Int;

    #[logic(open(self))]
    fn deep_model(self) -> Int {
        pearlite! { self.0@ }
    }
}

impl View for Variable {
    type ViewTy = Int;

    /// The clock index.
    #[logic(open(self))]
    fn view(self) -> Int {
        pearlite! { self.0@ }
    }
}

impl Variable {
    /// The actual clock with this index. `None` if `index == 0` or
    /// `index > MAX_VARIABLES`.
    #[check(terminates)]
    #[ensures(match result {
        Some(x) => 1 <= index@ && index@ <= MAX_VARIABLES@ && x@ == index@,
        None => index@ == 0 || index@ > MAX_VARIABLES@,
    })]
    pub const fn new(index: usize) -> Option<Variable> {
        if 1 <= index && index <= MAX_VARIABLES {
            Some(Variable(index as u32))
        } else {
            None
        }
    }

    /// The index (at least 1).
    #[check(terminates)]
    #[ensures(result@ == self@ && 1 <= result@)]
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

impl From<Variable> for Clock {
    /// The clock with the same index.
    #[check(terminates)]
    #[ensures(result@ == x@)]
    fn from(x: Variable) -> Clock {
        Clock(x.0)
    }
}

/// An actual clock is never the reference clock.
#[logic]
#[requires(inv(x))]
#[ensures(x@ != Clock::ZERO@)]
pub fn variable_not_zero(x: Variable) {}

/// A constraint on the difference between two clocks.
///
/// [`Constraint::le`] represents `x_i - x_j <= c` and [`Constraint::lt`]
/// represents `x_i - x_j < c`. Clock 0 is the fixed reference
/// [`Clock::ZERO`]. Constructing a constraint does not validate it against
/// a particular DBM; that happens when the constraint is applied.
///
/// # Example
///
/// ```
/// use clock_dbm::{Clock, Constraint};
/// # fn main() -> Result<(), clock_dbm::Error> {
/// let x = Clock::new(1).unwrap();
/// let y = Clock::new(2).unwrap();
/// let x_at_least_two = Constraint::le(Clock::ZERO, x, -2)?;
/// let x_minus_y_below_three = Constraint::lt(x, y, 3)?;
/// assert_eq!(x_at_least_two.i(), Clock::ZERO);
/// assert_eq!(x_minus_y_below_three.j(), y);
/// # Ok(())
/// # }
/// ```
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(not(creusot), derive(Hash))]
pub struct Constraint {
    i: Clock,
    j: Clock,
    bound: Bound,
}

impl DeepModel for Constraint {
    type DeepModelTy = (Int, Int, Int);

    #[logic(open(self))]
    fn deep_model(self) -> (Int, Int, Int) {
        pearlite! { (self.i.deep_model(), self.j.deep_model(), self.bound.deep_model()) }
    }
}

impl View for Constraint {
    type ViewTy = (Int, Int, BoundModel);

    /// `(i, j, b)`: the indices and the model of the bound.
    #[logic(open(self))]
    fn view(self) -> (Int, Int, BoundModel) {
        pearlite! { (self.i@, self.j@, self.bound@) }
    }
}

impl Constraint {
    /// Constructs a constraint on `clock i - clock j` using `bound`.
    ///
    /// The bound specifies either `< c`, `<= c`, or no restriction.
    /// Both clocks may be the same; validity for a particular zone is
    /// checked when the constraint is applied.
    #[check(terminates)]
    #[ensures(result@ == (i@, j@, bound@))]
    pub const fn new(i: Clock, j: Clock, bound: Bound) -> Constraint {
        Constraint { i, j, bound }
    }

    /// Constructs the constraint `clock i - clock j <= c`.
    ///
    /// Returns [`Error::Range`] if `c` is outside the supported bound range.
    #[check(terminates)]
    #[ensures(match result {
        Ok(g) => BoundModel::in_range(c@) && g@ == (i@, j@, BoundModel::Le(c@)),
        Err(e) => !BoundModel::in_range(c@) && e == Error::Range,
    })]
    pub const fn le(i: Clock, j: Clock, c: i32) -> Result<Constraint, Error> {
        match Bound::le(c) {
            Ok(bound) => Ok(Constraint { i, j, bound }),
            Err(e) => Err(e),
        }
    }

    /// Constructs the constraint `clock i - clock j < c`.
    ///
    /// Returns [`Error::Range`] if `c` is outside the supported bound range.
    #[check(terminates)]
    #[ensures(match result {
        Ok(g) => BoundModel::in_range(c@) && g@ == (i@, j@, BoundModel::Lt(c@)),
        Err(e) => !BoundModel::in_range(c@) && e == Error::Range,
    })]
    pub const fn lt(i: Clock, j: Clock, c: i32) -> Result<Constraint, Error> {
        match Bound::lt(c) {
            Ok(bound) => Ok(Constraint { i, j, bound }),
            Err(e) => Err(e),
        }
    }

    /// The minuend clock `x_i`.
    #[check(terminates)]
    #[ensures(result@ == self@.0)]
    pub const fn i(self) -> Clock {
        self.i
    }

    /// The subtrahend clock `x_j`.
    #[check(terminates)]
    #[ensures(result@ == self@.1)]
    pub const fn j(self) -> Clock {
        self.j
    }

    /// Returns the strict, non-strict, or infinite bound on the difference
    /// between the two clocks.
    #[check(terminates)]
    #[ensures(result@ == self@.2)]
    pub const fn bound(self) -> Bound {
        self.bound
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn le(c: i32) -> Bound {
        Bound::le(c).unwrap()
    }
    fn lt(c: i32) -> Bound {
        Bound::lt(c).unwrap()
    }

    #[test]
    fn codes() {
        assert_eq!(lt(3).0, 6);
        assert_eq!(le(3).0, 7);
        assert_eq!(lt(-3).0, -6);
        assert_eq!(le(-3).0, -5);
        assert_eq!(Bound::INFINITY.0, 0x7FFF_FFFE);
        assert_eq!(Bound::LE_ZERO, le(0));
        assert_eq!(Bound::LT_ZERO, lt(0));
    }

    #[test]
    fn literal_constants() {
        const {
            assert!(MAX_CONSTANT == (1 << 29) - 1);
            assert!(MIN_CONSTANT == -MAX_CONSTANT);
            assert!(MIN_CODE == 2 * MIN_CONSTANT);
            assert!(MAX_CODE == 2 * MAX_CONSTANT + 1);
            assert!(MAX_VARIABLES == 46_339);
            // Dimension safety: (n+1)² < 2³¹.
            assert!(((MAX_VARIABLES + 1) as u64).pow(2) < 1 << 31);
        }
    }

    #[test]
    fn relax_row_cases() {
        let inf = Bound::INFINITY;
        // dst = [Le 5, ∞, Lt 3, ∞, Le 0, Le 1], via = Le 2.
        let mut dst = [le(5), inf, lt(3), inf, le(0), le(1)];
        let src = [le(1), le(4), le(1), inf, lt(-2), le(-1)];
        assert!(!relax_row(&mut dst, le(2), &src));
        // 2+1 = Le 3 < Le 5; ∞ → Le 6; Le 3 not tighter than Lt 3; ∞ source
        // skipped; Lt 0 < Le 0; Le 1 is not strictly tighter than Le 1.
        assert_eq!(dst, [le(3), le(6), lt(3), inf, lt(0), le(1)]);

        // A needed unrepresentable sum is flagged and leaves the entry
        // unchanged; an unneeded one (above MAX, finite current) is not.
        let big = le(MAX_CONSTANT);
        let mut dst = [inf, le(0), lt(-MAX_CONSTANT)];
        let src = [big, big, lt(MIN_CONSTANT)];
        assert!(relax_row(&mut dst, le(1), &src));
        assert_eq!(dst[0], inf);
        assert_eq!(dst[1], le(0));
        let mut dst = [le(0)];
        assert!(!relax_row(&mut dst, le(1), &[big]));
        assert_eq!(dst, [le(0)]);
        // Below MIN_CONSTANT: tighter than everything, so needed and flagged.
        let mut dst = [lt(MIN_CONSTANT)];
        assert!(relax_row(&mut dst, le(-1), &[le(MIN_CONSTANT)]));
        assert_eq!(dst, [lt(MIN_CONSTANT)]);
    }

    #[test]
    fn codes_at_limits() {
        assert_eq!(le(MAX_CONSTANT).0, (1 << 30) - 1);
        assert_eq!(lt(MAX_CONSTANT).0, (1 << 30) - 2);
        assert_eq!(lt(MIN_CONSTANT).0, -(1 << 30) + 2);
        assert_eq!(le(MIN_CONSTANT).0, -(1 << 30) + 3);
        assert_eq!(MIN_CODE, lt(MIN_CONSTANT).0);
        assert_eq!(MAX_CODE, le(MAX_CONSTANT).0);
        // Headroom: valid codes are below the sentinel's neighbor, and the
        // sum of two codes (before the strictness correction) fits in i32.
        const {
            assert!(MAX_CODE < INF - 1);
            assert!(2 * (MIN_CODE as i64) > i32::MIN as i64);
            assert!(2 * (MAX_CODE as i64) < i32::MAX as i64);
        }
    }
}
