//! Reproducible random generation, a greedy shrinker and a seeded runner.
//!
//! The generator is SplitMix64, written out here so the random streams never
//! change with a dependency upgrade. Each property runs cases with seeds
//! `0..cases`; the environment variables below control it:
//!
//! - `ORACLE_SEED=<u64>`: run only this seed (replay a reported failure);
//! - `ORACLE_CASES=<u64>`: number of seeds per property (default: the
//!   property's own small count, so CI stays fast).
//!
//! A failing case is shrunk and reported with its seed, the original and
//! shrunk [`Scenario`] (as pasteable Rust) and the oracle trace.

use num_bigint::BigInt;
use num_rational::BigRational;

use super::scenario::{Op, Scenario, Start};
use super::valuation::Valuation;
use super::zone::{OracleConstraint, OracleDbm};

/// SplitMix64 (Steele, Lea and Flood 2014).
#[derive(Clone, Debug)]
pub struct SplitMix64 {
    state: u64,
}

impl SplitMix64 {
    /// A generator seeded with `seed`.
    pub fn new(seed: u64) -> SplitMix64 {
        SplitMix64 { state: seed }
    }

    /// The next 64 random bits.
    pub fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// Uniform in `0..n` (`n > 0`; the modulo bias is irrelevant here).
    pub fn below(&mut self, n: u64) -> u64 {
        assert!(n > 0);
        self.next_u64() % n
    }

    /// Uniform in `lo..=hi`.
    pub fn range(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        lo + self.below((hi - lo) as u64 + 1) as i64
    }

    /// True with probability `num / den`.
    pub fn chance(&mut self, num: u64, den: u64) -> bool {
        self.below(den) < num
    }

    /// A uniformly chosen index into a slice of length `len`.
    pub fn index(&mut self, len: usize) -> usize {
        self.below(len as u64) as usize
    }
}

/// FNV-1a, used to give each property its own random stream.
fn name_hash(name: &str) -> u64 {
    name.bytes().fold(0xcbf2_9ce4_8422_2325, |h, b| {
        (h ^ u64::from(b)).wrapping_mul(0x0100_0000_01b3)
    })
}

/// The generator for case `seed` of property `name`.
pub fn case_rng(name: &str, seed: u64) -> SplitMix64 {
    SplitMix64::new(name_hash(name) ^ seed.wrapping_mul(0x9E37_79B9_7F4A_7C15))
}

// ----- generators -----

/// A random constraint on clocks `0..=n` with constant in `[−max_c, max_c]`.
/// Includes `i = j`, guards against the reference clock, diagonal guards,
/// strict and weak bounds, and occasionally `∞`.
pub fn constraint(rng: &mut SplitMix64, n: usize, max_c: i64) -> OracleConstraint {
    let i = rng.index(n + 1);
    let j = rng.index(n + 1);
    if rng.chance(1, 16) {
        return super::scenario::inf(i, j);
    }
    let c = rng.range(-max_c, max_c);
    if rng.chance(1, 2) {
        OracleConstraint::lt(i, j, c)
    } else {
        OracleConstraint::le(i, j, c)
    }
}

/// A random valuation with values in `{0, 1/den, …, max}`.
pub fn valuation(rng: &mut SplitMix64, n: usize, max: i64, den: i64) -> Valuation {
    Valuation::new(
        (0..n)
            .map(|_| BigRational::new(rng.range(0, max * den).into(), den.into()))
            .collect(),
    )
}

/// `count` constraints all satisfied by a hidden valuation, which is also
/// returned. Constants are at most about `max_c + 2` in absolute value.
pub fn consistent_constraints(
    rng: &mut SplitMix64,
    n: usize,
    count: usize,
    max_c: i64,
) -> (Vec<OracleConstraint>, Valuation) {
    let u = valuation(rng, n, max_c, 2 * (n as i64 + 1));
    let cs = (0..count)
        .map(|_| {
            let i = rng.index(n + 1);
            let j = rng.index(n + 1);
            let diff = u.value(i) - u.value(j);
            let c = diff.ceil().to_integer() + BigInt::from(rng.range(0, 2));
            let strict = BigRational::from_integer(c.clone()) > diff && rng.chance(1, 2);
            if strict {
                OracleConstraint::lt(i, j, c)
            } else {
                OracleConstraint::le(i, j, c)
            }
        })
        .collect();
    (cs, u)
}

/// Constraints whose conjunction is empty: consistent ones plus a constraint
/// `(j, i, b)` with `D[i][j] + b ≺ Le 0`, tight or slightly tighter.
pub fn inconsistent_constraints(
    rng: &mut SplitMix64,
    n: usize,
    count: usize,
    max_c: i64,
) -> Vec<OracleConstraint> {
    let (mut cs, _) = consistent_constraints(rng, n, count, max_c);
    if n == 0 {
        // Only x0 − x0 can be constrained.
        cs.push(OracleConstraint::lt(0, 0, -rng.range(0, 1)));
        return cs;
    }
    let d = OracleDbm::from_constraints(n, &cs).expect("indices in range");
    let m = d.matrix().expect("consistent constraints are satisfiable");
    // Pick a finite canonical entry; D[0][k] is always finite.
    let finite: Vec<(usize, usize)> = (0..=n)
        .flat_map(|i| (0..=n).map(move |j| (i, j)))
        .filter(|&(i, j)| i != j && !m[i][j].is_infinite())
        .collect();
    let (i, j) = finite[rng.index(finite.len())];
    let neg = OracleConstraint::new(i, j, m[i][j].clone())
        .negated()
        .expect("finite");
    let slack = rng.range(0, 1);
    let c = neg.bound.constant().expect("finite") - BigInt::from(slack);
    cs.push(if neg.bound.is_strict() {
        OracleConstraint::lt(neg.i, neg.j, c)
    } else {
        OracleConstraint::le(neg.i, neg.j, c)
    });
    // Mix the contradiction into the batch.
    let last = cs.len() - 1;
    let k = rng.index(cs.len());
    cs.swap(k, last);
    cs
}

fn constraints(rng: &mut SplitMix64, n: usize, max_c: i64) -> Vec<OracleConstraint> {
    let count = rng.index(4) + 1;
    (0..count).map(|_| constraint(rng, n, max_c)).collect()
}

/// A random start zone; mostly nonempty, sometimes empty.
pub fn start(rng: &mut SplitMix64, n: usize) -> Start {
    match rng.below(12) {
        0 | 1 => Start::Zero,
        2 | 3 => Start::Universe,
        4 => Start::Empty,
        5..=8 => {
            let count = rng.index(2 * n + 2);
            Start::Constraints(consistent_constraints(rng, n, count, 6).0)
        }
        9 | 10 => Start::Constraints(constraints(rng, n, 6)),
        _ => {
            let count = rng.index(n + 2);
            Start::Constraints(inconsistent_constraints(rng, n, count, 6))
        }
    }
}

/// A random valid operation on `n` clocks.
pub fn op(rng: &mut SplitMix64, n: usize) -> Op {
    loop {
        let op = match rng.below(10) {
            0 | 1 => Op::Constrain(constraint(rng, n, 6)),
            2 => Op::ConstrainAll(constraints(rng, n, 6)),
            3 => Op::Intersect(constraints(rng, n, 6)),
            4 => Op::Future,
            5 if n > 0 => Op::Reset {
                x: rng.index(n) + 1,
                value: rng.range(0, 6),
            },
            6 if n > 0 => Op::ResetZero(rng.index(n) + 1),
            7 if n > 0 => Op::Free(rng.index(n) + 1),
            8 => Op::ExtrapolateMax((0..n).map(|_| rng.range(0, 6)).collect()),
            9 => Op::Past,
            _ => continue,
        };
        return op;
    }
}

/// A random scenario on `0..=max_variables` clocks with up to `max_ops` ops.
pub fn scenario(rng: &mut SplitMix64, max_variables: usize, max_ops: usize) -> Scenario {
    let variables = rng.index(max_variables + 1);
    let start = start(rng, variables);
    let len = rng.index(max_ops + 1);
    let ops = (0..len).map(|_| op(rng, variables)).collect();
    Scenario {
        variables,
        start,
        ops,
    }
}

// ----- shrinking -----

fn smaller_constants(c: &OracleConstraint) -> Vec<OracleConstraint> {
    let Some(k) = c.bound.constant() else {
        return Vec::new();
    };
    let zero = BigInt::from(0);
    if *k == zero {
        return Vec::new();
    }
    let step = if *k > zero {
        BigInt::from(1)
    } else {
        BigInt::from(-1)
    };
    let mut out = Vec::new();
    for k2 in [k / BigInt::from(2), k - step] {
        let bound = if c.bound.is_strict() {
            super::bound::ExactBound::lt(k2)
        } else {
            super::bound::ExactBound::le(k2)
        };
        out.push(OracleConstraint::new(c.i, c.j, bound));
    }
    out
}

fn smaller_lists(cs: &[OracleConstraint]) -> Vec<Vec<OracleConstraint>> {
    let mut out = Vec::new();
    for k in 0..cs.len() {
        let mut fewer = cs.to_vec();
        fewer.remove(k);
        out.push(fewer);
    }
    for (k, c) in cs.iter().enumerate() {
        for smaller in smaller_constants(c) {
            let mut v = cs.to_vec();
            v[k] = smaller;
            out.push(v);
        }
    }
    out
}

fn smaller_ints(v: i64) -> Vec<i64> {
    if v == 0 {
        Vec::new()
    } else {
        vec![v / 2, v - v.signum()]
    }
}

fn smaller_ops(op: &Op) -> Vec<Op> {
    match op {
        Op::Constrain(c) => smaller_constants(c)
            .into_iter()
            .map(Op::Constrain)
            .collect(),
        Op::ConstrainAll(cs) => {
            let mut out: Vec<Op> = smaller_lists(cs)
                .into_iter()
                .map(Op::ConstrainAll)
                .collect();
            if let [c] = cs.as_slice() {
                out.insert(0, Op::Constrain(c.clone()));
            }
            out
        }
        Op::Intersect(cs) => smaller_lists(cs).into_iter().map(Op::Intersect).collect(),
        Op::Reset { x, value } => {
            let mut out = vec![Op::ResetZero(*x)];
            out.extend(
                smaller_ints(*value)
                    .into_iter()
                    .map(|value| Op::Reset { x: *x, value }),
            );
            out
        }
        Op::ExtrapolateMax(m) => (0..m.len())
            .flat_map(|k| {
                smaller_ints(m[k]).into_iter().map(move |v| {
                    let mut m = m.clone();
                    m[k] = v;
                    Op::ExtrapolateMax(m)
                })
            })
            .collect(),
        Op::Future | Op::Past | Op::ResetZero(_) | Op::Free(_) => Vec::new(),
    }
}

/// Every one-step simplification of `s`. Each candidate is strictly smaller
/// (fewer ops or constraints, or constants closer to 0), so shrinking ends.
fn candidates(s: &Scenario) -> Vec<Scenario> {
    let mut out = Vec::new();
    for k in 0..s.ops.len() {
        let mut t = s.clone();
        t.ops.remove(k);
        out.push(t);
    }
    if let Start::Constraints(cs) = &s.start {
        let mut t = s.clone();
        t.start = Start::Universe;
        out.push(t);
        for smaller in smaller_lists(cs) {
            let mut t = s.clone();
            t.start = Start::Constraints(smaller);
            out.push(t);
        }
    }
    for (k, op) in s.ops.iter().enumerate() {
        for smaller in smaller_ops(op) {
            let mut t = s.clone();
            t.ops[k] = smaller;
            out.push(t);
        }
    }
    out
}

/// Greedily simplifies `s` while `fails` keeps returning true.
pub fn shrink(s: &Scenario, mut fails: impl FnMut(&Scenario) -> bool) -> Scenario {
    let mut current = s.clone();
    'outer: for _ in 0..10_000 {
        for candidate in candidates(&current) {
            if fails(&candidate) {
                current = candidate;
                continue 'outer;
            }
        }
        break;
    }
    current
}

// ----- runner -----

fn env_u64(name: &str) -> Option<u64> {
    let value = std::env::var(name).ok()?;
    Some(
        value
            .trim()
            .parse()
            .unwrap_or_else(|_| panic!("{name}={value:?} is not a u64")),
    )
}

/// The seeds to run: `ORACLE_SEED` alone if set, else `0..ORACLE_CASES` (or
/// `0..default_cases`).
pub fn seeds(default_cases: u64) -> std::ops::Range<u64> {
    match env_u64("ORACLE_SEED") {
        Some(seed) => seed..seed + 1,
        None => 0..env_u64("ORACLE_CASES").unwrap_or(default_cases),
    }
}

/// Runs property `name` on generated scenarios. Name the property after its
/// `#[test]` function so the printed replay command selects it.
///
/// For each seed, `generate` builds a scenario from `case_rng(name, seed)` and
/// `check` receives it together with a fresh auxiliary generator (for sample
/// points) derived from the same seed, so `check` is deterministic and can be
/// re-run while shrinking. On failure this panics with a replay report.
pub fn check_scenarios(
    name: &str,
    default_cases: u64,
    mut generate: impl FnMut(&mut SplitMix64) -> Scenario,
    mut check: impl FnMut(&Scenario, &mut SplitMix64) -> Result<(), String>,
) {
    for seed in seeds(default_cases) {
        let scenario = generate(&mut case_rng(name, seed));
        let aux = || case_rng(&format!("{name}/aux"), seed);
        if let Err(error) = check(&scenario, &mut aux()) {
            let shrunk = shrink(&scenario, |s| check(s, &mut aux()).is_err());
            let shrunk_error = check(&shrunk, &mut aux()).expect_err("shrunk case fails");
            let trace = match shrunk.run_oracle() {
                Ok(t) => t
                    .iter()
                    .enumerate()
                    .map(|(k, z)| format!("step {k}: {z}"))
                    .collect::<String>(),
                Err(e) => format!("{e:?}\n"),
            };
            // An integration test crate is named after its file.
            let test_file = module_path!().split("::").next().unwrap_or("<file>");
            panic!(
                "property (test) `{name}` failed for seed {seed}\n\
                 replay: ORACLE_SEED={seed} cargo test --test {test_file} {name}\n\n\
                 error: {error}\n\noriginal scenario:\n{scenario}\n\n\
                 shrunk scenario:\n{shrunk}\n\nshrunk error: {shrunk_error}\n\n\
                 oracle trace of the shrunk scenario:\n{trace}"
            );
        }
    }
}
