//! Tests of `Bound`, `Clock`, `Variable` and `Constraint` against the
//! public contracts of the bound, clock and constraint types.
//!
//! The property tests compare the packed implementation with an independent,
//! unpacked model (`M` below) that uses `i64` constants and its own order and
//! addition. They never look at packed codes.

use clock_dbm::{
    Bound, Clock, Constraint, Error, MAX_CONSTANT, MAX_VARIABLES, MIN_CONSTANT, Variable,
};
use std::cmp::Ordering;

fn le(c: i32) -> Bound {
    Bound::le(c).unwrap()
}
fn lt(c: i32) -> Bound {
    Bound::lt(c).unwrap()
}
const INF: Bound = Bound::INFINITY;

// ---------------------------------------------------------------------------
// Independent mathematical model of bounds.

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum M {
    Lt(i64),
    Le(i64),
    Inf,
}

impl M {
    fn in_range(c: i64) -> bool {
        (-(1 << 29) + 1..=(1 << 29) - 1).contains(&c)
    }

    /// Tightness order: `Lt c ≺ Le c ≺ Lt (c+1)`, everything finite `≺ ∞`.
    fn cmp(self, other: M) -> Ordering {
        // Rank of a finite bound on the real line: (constant, weak?).
        fn key(m: M) -> Option<(i64, bool)> {
            match m {
                M::Lt(c) => Some((c, false)),
                M::Le(c) => Some((c, true)),
                M::Inf => None,
            }
        }
        match (key(self), key(other)) {
            (None, None) => Ordering::Equal,
            (None, Some(_)) => Ordering::Greater,
            (Some(_), None) => Ordering::Less,
            (Some(a), Some(b)) => a.cmp(&b),
        }
    }

    /// `dbm_add`: strict iff either summand is strict; `∞` absorbs.
    fn add(self, other: M) -> M {
        match (self, other) {
            (M::Inf, _) | (_, M::Inf) => M::Inf,
            (M::Le(a), M::Le(b)) => M::Le(a + b),
            (M::Lt(a) | M::Le(a), M::Lt(b) | M::Le(b)) => M::Lt(a + b),
        }
    }

    fn constant(self) -> Option<i64> {
        match self {
            M::Lt(c) | M::Le(c) => Some(c),
            M::Inf => None,
        }
    }

    /// Packs through the public constructors only.
    fn pack(self) -> Result<Bound, Error> {
        let narrow = |c: i64| i32::try_from(c).map_err(|_| Error::Range);
        match self {
            M::Lt(c) => Bound::lt(narrow(c)?),
            M::Le(c) => Bound::le(narrow(c)?),
            M::Inf => Ok(Bound::INFINITY),
        }
    }

    /// Reads a bound back through the public accessors only.
    fn of(b: Bound) -> M {
        match b.constant() {
            None => {
                assert!(b.is_infinite() && !b.is_strict());
                M::Inf
            }
            Some(c) => {
                assert!(!b.is_infinite());
                if b.is_strict() {
                    M::Lt(c.into())
                } else {
                    M::Le(c.into())
                }
            }
        }
    }
}

/// SplitMix64: a tiny deterministic generator, so runs are reproducible
/// without extra dependencies.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// A constant biased toward the interesting places: zero, both range
    /// limits and just outside them, small values, and arbitrary `i32`s.
    fn constant(&mut self) -> i64 {
        let max = i64::from(MAX_CONSTANT);
        let jitter = (self.next() % 5) as i64 - 2;
        match self.next() % 6 {
            0 => jitter,
            1 => max + jitter,
            2 => -max + jitter,
            3 => max / 2 + jitter,
            4 => (self.next() % 2001) as i64 - 1000,
            _ => i64::from(self.next() as i32),
        }
    }

    fn model(&mut self) -> M {
        let c = self.constant();
        match self.next() % 7 {
            0 => M::Inf,
            1..=3 => M::Lt(c),
            _ => M::Le(c),
        }
    }
}

/// Every finite model with a constant near 0 or near a range limit, plus `∞`.
fn boundary_models() -> Vec<M> {
    let max = i64::from(MAX_CONSTANT);
    let mut v = vec![M::Inf];
    for centre in [0, max, -max, max / 2, -max / 2] {
        for c in centre - 3..=centre + 3 {
            v.push(M::Lt(c));
            v.push(M::Le(c));
        }
    }
    v
}

/// Checks every public bound operation on one pair of models.
fn check_pair(a: M, b: M) {
    let (Ok(pa), Ok(pb)) = (a.pack(), b.pack()) else {
        return;
    };
    assert_eq!(M::of(pa), a);
    assert_eq!(pa.cmp(&pb), a.cmp(b), "{a:?} vs {b:?}");
    assert_eq!(pa == pb, a == b);
    assert_eq!(M::of(pa.min(pb)), if a.cmp(b).is_le() { a } else { b });
    let sum = a.add(b);
    let representable = sum.constant().is_none_or(M::in_range);
    match pa.checked_add(pb) {
        Ok(r) => {
            assert!(representable, "{a:?} + {b:?} should be out of range");
            assert_eq!(M::of(r), sum, "{a:?} + {b:?}");
        }
        Err(e) => {
            assert!(!representable, "{a:?} + {b:?} should be {sum:?}");
            assert_eq!(e, Error::Range);
        }
    }
}

// ---------------------------------------------------------------------------
// Constructors and accessors.

#[test]
fn constants() {
    assert_eq!(MAX_CONSTANT, (1 << 29) - 1);
    assert_eq!(MIN_CONSTANT, -MAX_CONSTANT);
    assert_eq!(Bound::LE_ZERO, le(0));
    assert_eq!(Bound::LT_ZERO, lt(0));
    assert!(INF.is_infinite());
    assert_eq!(INF.constant(), None);
    assert!(!INF.is_strict());
}

#[test]
fn accessors() {
    assert_eq!(lt(-7).constant(), Some(-7));
    assert!(lt(-7).is_strict());
    assert_eq!(le(-7).constant(), Some(-7));
    assert!(!le(-7).is_strict());
    assert!(!le(0).is_infinite());
    assert_eq!(le(MAX_CONSTANT).constant(), Some(MAX_CONSTANT));
    assert_eq!(lt(MIN_CONSTANT).constant(), Some(MIN_CONSTANT));
}

#[test]
fn constructor_limits() {
    for c in [
        MIN_CONSTANT,
        MIN_CONSTANT + 1,
        -1,
        0,
        1,
        MAX_CONSTANT - 1,
        MAX_CONSTANT,
    ] {
        assert!(Bound::le(c).is_ok(), "le({c})");
        assert!(Bound::lt(c).is_ok(), "lt({c})");
    }
    for c in [
        i32::MIN,
        i32::MIN + 1,
        MIN_CONSTANT - 1,
        MAX_CONSTANT + 1,
        // Constants whose naive codes would be the sentinel or its neighbors.
        0x3FFF_FFFF,
        0x3FFF_FFFE,
        i32::MAX - 1,
        i32::MAX,
    ] {
        assert_eq!(Bound::le(c), Err(Error::Range), "le({c})");
        assert_eq!(Bound::lt(c), Err(Error::Range), "lt({c})");
    }
}

// ---------------------------------------------------------------------------
// Addition of strict and weak bounds.

#[test]
fn addition_truth_table() {
    assert_eq!(lt(2).checked_add(le(3)), Ok(lt(5)));
    assert_eq!(le(2).checked_add(lt(3)), Ok(lt(5)));
    assert_eq!(lt(2).checked_add(lt(3)), Ok(lt(5)));
    assert_eq!(le(2).checked_add(le(3)), Ok(le(5)));
    // Infinity absorbs, whatever the other summand.
    for b in [
        lt(2),
        le(2),
        lt(-4),
        le(MIN_CONSTANT),
        le(MAX_CONSTANT),
        INF,
    ] {
        assert_eq!(INF.checked_add(b), Ok(INF));
        assert_eq!(b.checked_add(INF), Ok(INF));
    }
}

#[test]
fn addition_zeros_and_negatives() {
    assert_eq!(le(0).checked_add(le(0)), Ok(le(0)));
    assert_eq!(lt(0).checked_add(le(0)), Ok(lt(0)));
    assert_eq!(le(0).checked_add(lt(0)), Ok(lt(0)));
    assert_eq!(lt(0).checked_add(lt(0)), Ok(lt(0)));
    assert_eq!(le(-3).checked_add(le(-4)), Ok(le(-7)));
    assert_eq!(lt(-3).checked_add(le(-4)), Ok(lt(-7)));
    assert_eq!(le(5).checked_add(lt(-5)), Ok(lt(0)));
    assert_eq!(le(5).checked_add(le(-5)), Ok(le(0)));
    // A negative cycle weight (closure's emptiness signal) is an ordinary value.
    assert_eq!(le(3).checked_add(lt(-3)), Ok(lt(0)));
    assert_eq!(le(3).checked_add(le(-4)), Ok(le(-1)));
}

#[test]
fn addition_range_limits() {
    let max = MAX_CONSTANT;
    let min = MIN_CONSTANT;
    // Exactly at the limits.
    assert_eq!(le(max - 1).checked_add(le(1)), Ok(le(max)));
    assert_eq!(lt(max).checked_add(le(0)), Ok(lt(max)));
    assert_eq!(le(min + 1).checked_add(lt(-1)), Ok(lt(min)));
    assert_eq!(le(min).checked_add(le(0)), Ok(le(min)));
    assert_eq!(le(max).checked_add(le(min)), Ok(le(0)));
    // Just past the limits: a range error, never ∞ and never a clamp.
    assert_eq!(le(max).checked_add(le(1)), Err(Error::Range));
    assert_eq!(lt(max).checked_add(lt(1)), Err(Error::Range));
    assert_eq!(le(min).checked_add(lt(-1)), Err(Error::Range));
    assert_eq!(lt(min).checked_add(le(-1)), Err(Error::Range));
    // The extreme sums stay range errors (and do not overflow i32).
    assert_eq!(le(max).checked_add(le(max)), Err(Error::Range));
    assert_eq!(lt(max).checked_add(le(max)), Err(Error::Range));
    assert_eq!(lt(min).checked_add(lt(min)), Err(Error::Range));
    assert_eq!(le(min).checked_add(lt(min)), Err(Error::Range));
}

// ---------------------------------------------------------------------------
// Tightness ordering.

#[test]
fn tightness_order() {
    assert!(lt(3) < le(3));
    assert!(le(3) < lt(4));
    assert!(le(MAX_CONSTANT) < INF);
    assert!(lt(MIN_CONSTANT) < le(MIN_CONSTANT));
    assert!(le(-1) < lt(0));
    assert!(lt(0) < le(0));
    assert_eq!(lt(3).min(le(3)), lt(3));
    assert_eq!(le(3).max(lt(3)), le(3));
    assert_eq!(INF.min(le(-5)), le(-5));
    assert_eq!(INF.max(le(-5)), INF);
    let mut v = vec![INF, le(2), lt(2), le(-1), lt(3), lt(-1), le(MIN_CONSTANT)];
    v.sort();
    assert_eq!(
        v,
        [le(MIN_CONSTANT), lt(-1), le(-1), lt(2), le(2), lt(3), INF]
    );
}

// ---------------------------------------------------------------------------
// Property tests against the unpacked model.

#[test]
fn exhaustive_boundary_pairs() {
    let models = boundary_models();
    for &a in &models {
        for &b in &models {
            check_pair(a, b);
        }
    }
}

#[test]
fn random_pairs() {
    let mut rng = Rng(0x00C1_0C4D_B300_0004);
    for _ in 0..200_000 {
        let (a, b) = (rng.model(), rng.model());
        // Constructors agree with the model's range on every generated input.
        for m in [a, b] {
            let expect = m.constant().is_none_or(M::in_range);
            assert_eq!(m.pack().is_ok(), expect, "{m:?}");
        }
        check_pair(a, b);
    }
}

#[test]
fn addition_laws() {
    // Commutativity, associativity (when every partial sum is representable)
    // and the unit Le(0), on random bounds.
    let mut rng = Rng(42);
    for _ in 0..50_000 {
        let [a, b, c] = [rng.model(), rng.model(), rng.model()];
        let (Ok(pa), Ok(pb), Ok(pc)) = (a.pack(), b.pack(), c.pack()) else {
            continue;
        };
        assert_eq!(pa.checked_add(pb), pb.checked_add(pa));
        assert_eq!(pa.checked_add(Bound::LE_ZERO), Ok(pa));
        if let (Ok(ab), Ok(bc)) = (pa.checked_add(pb), pb.checked_add(pc)) {
            assert_eq!(ab.checked_add(pc), pa.checked_add(bc));
        }
    }
}

// ---------------------------------------------------------------------------
// Clocks and variables.

#[test]
fn clocks() {
    assert_eq!(Clock::ZERO.index(), 0);
    assert_eq!(Clock::new(0), Some(Clock::ZERO));
    assert_eq!(
        Clock::new(MAX_VARIABLES).map(Clock::index),
        Some(MAX_VARIABLES)
    );
    assert_eq!(Clock::new(MAX_VARIABLES + 1), None);
    assert_eq!(Clock::new(usize::MAX), None);
    assert!(Clock::new(1) < Clock::new(2));
}

#[test]
fn variables() {
    assert_eq!(Variable::new(0), None);
    assert_eq!(Variable::new(1).map(Variable::index), Some(1));
    assert_eq!(
        Variable::new(MAX_VARIABLES).map(Variable::index),
        Some(MAX_VARIABLES)
    );
    assert_eq!(Variable::new(MAX_VARIABLES + 1), None);
    assert_eq!(Variable::new(usize::MAX), None);
    let x = Variable::new(3).unwrap();
    let c: Clock = x.into();
    assert_eq!(c.index(), 3);
    assert_ne!(c, Clock::ZERO);
}

// ---------------------------------------------------------------------------
// Difference constraints.

#[test]
fn constraints() {
    let x: Clock = Variable::new(1).unwrap().into();
    let y: Clock = Variable::new(2).unwrap().into();

    // x ≥ 3  is  0 − x ≤ −3.
    let g = Constraint::le(Clock::ZERO, x, -3).unwrap();
    assert_eq!((g.i(), g.j(), g.bound()), (Clock::ZERO, x, le(-3)));
    // x < 5  is  x − 0 < 5.
    let g = Constraint::lt(x, Clock::ZERO, 5).unwrap();
    assert_eq!((g.i(), g.j(), g.bound()), (x, Clock::ZERO, lt(5)));
    // x − y ≤ 2, and the general constructor.
    let g = Constraint::le(x, y, 2).unwrap();
    assert_eq!(g, Constraint::new(x, y, le(2)));
    // i == j is allowed.
    assert_eq!(Constraint::lt(x, x, 0).unwrap().bound(), lt(0));
    assert_eq!(Constraint::new(y, x, INF).bound(), INF);

    // Range errors.
    assert_eq!(Constraint::le(x, y, MAX_CONSTANT + 1), Err(Error::Range));
    assert_eq!(Constraint::lt(x, y, i32::MIN), Err(Error::Range));
}

#[test]
fn lower_bound_guards_at_the_limits() {
    // The symmetric range makes negation total: x ≥ c and x > c are
    // representable for every representable c.
    let x: Clock = Variable::new(1).unwrap().into();
    for c in [0, 1, MAX_CONSTANT, MIN_CONSTANT] {
        let g = Constraint::le(Clock::ZERO, x, -c).unwrap();
        assert_eq!(g.bound().constant(), Some(-c));
        let g = Constraint::lt(Clock::ZERO, x, -c).unwrap();
        assert_eq!(g.bound().constant(), Some(-c));
    }
}

#[test]
fn errors_display() {
    assert!(Error::Range.to_string().contains("range"));
    let e: Box<dyn std::error::Error> = Box::new(Error::NegativeConstant { value: -1 });
    assert!(e.to_string().contains("-1"));
}
