//! Integration tests of the exported `constraint!` macro: its results must
//! agree exactly with the `Constraint::lt` / `Constraint::le` constructors,
//! for both the difference forms and the single-clock forms.

use clock_dbm::{
    Clock, Constraint, Dbm, Error, MAX_CONSTANT, MIN_CONSTANT, Variable, Workspace, constraint,
};
use std::cell::Cell;

fn clock(i: usize) -> Clock {
    Clock::new(i).unwrap()
}

#[test]
fn strict_and_weak() {
    let (x, y) = (clock(1), clock(2));
    let strict = constraint!(y - x < 3).unwrap();
    let weak = constraint!(y - x <= 3).unwrap();
    assert_eq!(strict, Constraint::lt(y, x, 3).unwrap());
    assert_eq!(weak, Constraint::le(y, x, 3).unwrap());
    assert_ne!(strict, weak);
    // `y - x` is x_i − x_j with i = y, j = x.
    assert_eq!((strict.i(), strict.j()), (y, x));
}

#[test]
fn positive_negative_and_zero_bounds() {
    let (x, y) = (clock(1), clock(3));
    for c in [-7, -1, 0, 1, 7, MIN_CONSTANT, MAX_CONSTANT] {
        assert_eq!(constraint!(y - x < c), Constraint::lt(y, x, c));
        assert_eq!(constraint!(y - x <= c), Constraint::le(y, x, c));
    }
    assert_eq!(constraint!(y - x < -4), Constraint::lt(y, x, -4));
    assert_eq!(constraint!(y - x <= -4), Constraint::le(y, x, -4));
}

#[test]
fn bound_expressions() {
    let (x, y) = (clock(1), clock(2));
    let k = 4;
    let twice = |n: i32| 2 * n;
    assert_eq!(constraint!(y - x < k + 1), Constraint::lt(y, x, 5));
    assert_eq!(constraint!(y - x <= -k), Constraint::le(y, x, -4));
    assert_eq!(constraint!(y - x <= twice(k)), Constraint::le(y, x, 8));
    assert_eq!(
        constraint!(y - x < if k > 0 { k } else { 0 }),
        Constraint::lt(y, x, 4)
    );
}

#[test]
fn clock_and_variable_operands() {
    let (vx, vy) = (Variable::new(1).unwrap(), Variable::new(2).unwrap());
    let (x, y) = (Clock::from(vx), Clock::from(vy));
    let expected = Constraint::le(y, x, 2).unwrap();
    assert_eq!(constraint!(vy - vx <= 2).unwrap(), expected);
    assert_eq!(constraint!(vy - x <= 2).unwrap(), expected);
    assert_eq!(constraint!(y - vx <= 2).unwrap(), expected);
    assert_eq!(constraint!(y - x <= 2).unwrap(), expected);
}

#[test]
fn reference_clock_through_a_binding() {
    let x = Variable::new(1).unwrap();
    let zero = Clock::ZERO;
    let lower = constraint!(zero - x <= -2).unwrap(); // x ≥ 2
    let upper = constraint!(x - zero < 5).unwrap(); // x < 5
    assert_eq!(lower, Constraint::le(Clock::ZERO, x.into(), -2).unwrap());
    assert_eq!(upper, Constraint::lt(x.into(), Clock::ZERO, 5).unwrap());
    assert_eq!(lower.i(), Clock::ZERO);
}

#[test]
fn range_errors_are_propagated() {
    let (x, y) = (clock(1), clock(2));
    assert_eq!(constraint!(y - x < MAX_CONSTANT + 1), Err(Error::Range));
    assert_eq!(constraint!(y - x <= MAX_CONSTANT + 1), Err(Error::Range));
    assert_eq!(constraint!(y - x < MIN_CONSTANT - 1), Err(Error::Range));
    assert_eq!(constraint!(y - x <= i32::MIN), Err(Error::Range));

    fn guard(x: Clock, y: Clock, c: i32) -> Result<Constraint, Error> {
        let g = constraint!(y - x <= c)?;
        Ok(g)
    }
    assert_eq!(guard(x, y, 3), Constraint::le(y, x, 3));
    assert_eq!(guard(x, y, i32::MAX), Err(Error::Range));
}

#[test]
fn bound_is_evaluated_once() {
    let (x, y) = (clock(1), clock(2));
    let calls = Cell::new(0);
    let bound = || {
        calls.set(calls.get() + 1);
        3
    };
    let _ = constraint!(y - x < bound());
    let _ = constraint!(y - x <= bound());
    assert_eq!(calls.get(), 2);
}

const ZERO: Clock = Clock::ZERO;

#[test]
fn single_clock_upper_bounds() {
    let x = clock(1);
    for c in [-7, -1, 0, 1, 7, MIN_CONSTANT, MAX_CONSTANT] {
        assert_eq!(constraint!(x < c), Constraint::lt(x, ZERO, c));
        assert_eq!(constraint!(x <= c), Constraint::le(x, ZERO, c));
    }
    let (strict, weak) = (constraint!(x < 5).unwrap(), constraint!(x <= 5).unwrap());
    assert_ne!(strict, weak);
    assert_eq!((strict.i(), strict.j()), (x, ZERO));
    assert_eq!((weak.i(), weak.j()), (x, ZERO));
}

#[test]
fn single_clock_lower_bounds() {
    let x = clock(1);
    for c in [-7, -1, 0, 1, 7, MIN_CONSTANT, MAX_CONSTANT] {
        assert_eq!(constraint!(x > c), Constraint::lt(ZERO, x, -c));
        assert_eq!(constraint!(x >= c), Constraint::le(ZERO, x, -c));
    }
    let (strict, weak) = (constraint!(x > 2).unwrap(), constraint!(x >= 2).unwrap());
    assert_ne!(strict, weak);
    assert_eq!((strict.i(), strict.j()), (ZERO, x));
    assert_eq!((weak.i(), weak.j()), (ZERO, x));
}

#[test]
fn single_clock_forms_match_explicit_reference_clock() {
    let x = clock(2);
    let zero = Clock::ZERO;
    for c in [-3, 0, 4] {
        assert_eq!(constraint!(x < c), constraint!(x - zero < c));
        assert_eq!(constraint!(x <= c), constraint!(x - zero <= c));
        assert_eq!(constraint!(x > c), constraint!(zero - x < -c));
        assert_eq!(constraint!(x >= c), constraint!(zero - x <= -c));
    }
}

#[test]
fn single_clock_variable_operands() {
    let v = Variable::new(3).unwrap();
    let x = Clock::from(v);
    assert_eq!(constraint!(v < 4), Constraint::lt(x, ZERO, 4));
    assert_eq!(constraint!(v <= 4), Constraint::le(x, ZERO, 4));
    assert_eq!(constraint!(v > 4), Constraint::lt(ZERO, x, -4));
    assert_eq!(constraint!(v >= 4), Constraint::le(ZERO, x, -4));
}

#[test]
fn single_clock_bound_expressions() {
    let x = clock(1);
    let k = 4;
    let twice = |n: i32| 2 * n;
    assert_eq!(constraint!(x < k + 1), Constraint::lt(x, ZERO, 5));
    assert_eq!(constraint!(x <= twice(k)), Constraint::le(x, ZERO, 8));
    // `-k` is negated again: x >= -4 is 0 - x <= 4.
    assert_eq!(constraint!(x >= -k), Constraint::le(ZERO, x, 4));
    assert_eq!(constraint!(x > k - 1), Constraint::lt(ZERO, x, -3));
    assert_eq!(
        constraint!(x >= if k > 0 { k } else { 0 }),
        Constraint::le(ZERO, x, -4)
    );
}

#[test]
fn single_clock_bound_is_evaluated_once() {
    let x = clock(1);
    let calls = Cell::new(0);
    let bound = || {
        calls.set(calls.get() + 1);
        3
    };
    let _ = constraint!(x < bound());
    let _ = constraint!(x <= bound());
    let _ = constraint!(x > bound());
    let _ = constraint!(x >= bound());
    assert_eq!(calls.get(), 4);
}

#[test]
fn single_clock_range_errors() {
    let x = clock(1);
    for c in [MAX_CONSTANT + 1, MIN_CONSTANT - 1, i32::MIN, i32::MAX] {
        assert_eq!(constraint!(x < c), Err(Error::Range));
        assert_eq!(constraint!(x <= c), Err(Error::Range));
        // `i32::MIN` cannot be negated; the others negate out of range.
        assert_eq!(constraint!(x > c), Err(Error::Range));
        assert_eq!(constraint!(x >= c), Err(Error::Range));
    }
    // The extreme representable lower bounds are accepted.
    assert_eq!(
        constraint!(x >= MAX_CONSTANT),
        Constraint::le(ZERO, x, MIN_CONSTANT)
    );
    assert_eq!(
        constraint!(x > MIN_CONSTANT),
        Constraint::lt(ZERO, x, MAX_CONSTANT)
    );

    fn lower(x: Clock, c: i32) -> Result<Constraint, Error> {
        let g = constraint!(x >= c)?;
        Ok(g)
    }
    assert_eq!(lower(x, 2), Constraint::le(ZERO, x, -2));
    assert_eq!(lower(x, i32::MIN), Err(Error::Range));
}

#[test]
fn single_clock_zone() -> Result<(), Error> {
    let (x, y) = (clock(1), clock(2));
    let mut ws = Workspace::new();
    let natural = Dbm::try_from_constraints(
        2,
        &[
            constraint!(x >= 2)?,
            constraint!(x <= 10)?,
            constraint!(y > 1)?,
            constraint!(y - x < 3)?,
        ],
        &mut ws,
    )?;
    let explicit = Dbm::try_from_constraints(
        2,
        &[
            Constraint::le(ZERO, x, -2)?,
            Constraint::le(x, ZERO, 10)?,
            Constraint::lt(ZERO, y, -1)?,
            Constraint::lt(y, x, 3)?,
        ],
        &mut ws,
    )?;
    assert!(!natural.is_empty());
    assert_eq!(natural, explicit);
    assert!(natural.entails(&constraint!(x > 1)?)?);
    assert!(!natural.entails(&constraint!(x > 2)?)?);
    Ok(())
}
