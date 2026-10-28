//! A concise syntax for constructing difference constraints.

/// A clock constraint written as a single-clock bound such as `x >= 2`, or
/// as a clock difference such as `y - x < 3`.
///
/// A constraint restricts the difference `xᵢ - xⱼ` of two clocks by an
/// integer `c`, either strictly (`< c`) or non-strictly (`<= c`). A plain
/// bound on one clock `x` is the difference `x - x₀`, where `x₀` is the
/// reference clock [`Clock::ZERO`], whose value is always `0`. The macro
/// supplies `x₀` itself for the single-clock forms:
///
/// | Macro form                 | Meaning      | Result                              |
/// |----------------------------|--------------|-------------------------------------|
/// | `constraint!(x < c)`       | `x < c`      | `Constraint::lt(x, Clock::ZERO, c)` |
/// | `constraint!(x <= c)`      | `x <= c`     | `Constraint::le(x, Clock::ZERO, c)` |
/// | `constraint!(x > c)`       | `x > c`      | `Constraint::lt(Clock::ZERO, x, -c)`|
/// | `constraint!(x >= c)`      | `x >= c`     | `Constraint::le(Clock::ZERO, x, -c)`|
/// | `constraint!(i - j < c)`   | `i - j < c`  | `Constraint::lt(i, j, c)`           |
/// | `constraint!(i - j <= c)`  | `i - j <= c` | `Constraint::le(i, j, c)`           |
///
/// Lower bounds are rewritten as upper bounds on `x₀ - x`: `x >= c` holds
/// exactly when `0 - x <= -c`, and `x > c` exactly when `0 - x < -c`.
///
/// - `x`, `i` and `j` are identifiers bound to a [`Clock`] or a
///   [`Variable`]. A [`Variable`] is converted with `Clock::from`.
/// - `c` is any `i32` expression. Every operand is evaluated exactly once.
///
/// The macro returns `Result<Constraint, Error>`, delegating to
/// [`Constraint::lt`] and [`Constraint::le`]. For lower bounds, it first
/// checks that negating the constant is representable.
///
/// # Errors
///
/// [`Error::Range`] if the stored constant is outside the range from
/// [`MIN_CONSTANT`] to [`MAX_CONSTANT`]. The stored constant is `c` for the
/// `<`, `<=` and difference forms, and `-c` for `>` and `>=`. In particular,
/// `x > i32::MIN` and `x >= i32::MIN` return [`Error::Range`] because `-c`
/// is not an `i32`; the negation never panics or wraps.
///
/// # Unsupported forms
///
/// `>` and `>=` between two clocks (`y - x >= 3`), other clock expressions,
/// and combinations of constraints are rejected at compile time:
///
/// ```compile_fail
/// use clock_dbm::{Clock, constraint};
///
/// let x = Clock::new(1).unwrap();
/// let y = Clock::new(2).unwrap();
/// let _ = constraint!(y - x >= 3);
/// ```
///
/// # Examples
///
/// ```
/// use clock_dbm::{Clock, Constraint, Variable, constraint};
///
/// let x = Clock::new(1).unwrap();
/// let y = Variable::new(2).unwrap();
///
/// assert_eq!(constraint!(x <= 10)?, Constraint::le(x, Clock::ZERO, 10)?);
/// assert_eq!(constraint!(x < 5)?, Constraint::lt(x, Clock::ZERO, 5)?);
/// assert_eq!(constraint!(x >= 2)?, Constraint::le(Clock::ZERO, x, -2)?);
/// assert_eq!(constraint!(x > 2)?, Constraint::lt(Clock::ZERO, x, -2)?);
///
/// let guard = constraint!(y - x < 3)?;
/// assert_eq!(guard, Constraint::lt(y.into(), x, 3)?);
///
/// let k = 5;
/// let invariant = constraint!(y <= 2 * k)?;
/// assert_eq!(invariant, Constraint::le(y.into(), Clock::ZERO, 10)?);
/// # Ok::<(), clock_dbm::Error>(())
/// ```
///
/// An unrepresentable bound is an error, as for the constructors:
///
/// ```
/// use clock_dbm::{Clock, Error, MAX_CONSTANT, constraint};
///
/// let x = Clock::new(1).unwrap();
/// assert_eq!(constraint!(x <= MAX_CONSTANT + 1), Err(Error::Range));
/// assert_eq!(constraint!(x >= i32::MIN), Err(Error::Range));
/// ```
///
/// [`Constraint::lt`]: crate::Constraint::lt
/// [`Constraint::le`]: crate::Constraint::le
/// [`Clock`]: crate::Clock
/// [`Clock::ZERO`]: crate::Clock::ZERO
/// [`Variable`]: crate::Variable
/// [`Error::Range`]: crate::Error::Range
/// [`MIN_CONSTANT`]: crate::MIN_CONSTANT
/// [`MAX_CONSTANT`]: crate::MAX_CONSTANT
#[macro_export]
macro_rules! constraint {
    ($i:ident - $j:ident < $c:expr) => {
        $crate::Constraint::lt($crate::Clock::from($i), $crate::Clock::from($j), $c)
    };
    ($i:ident - $j:ident <= $c:expr) => {
        $crate::Constraint::le($crate::Clock::from($i), $crate::Clock::from($j), $c)
    };
    ($x:ident < $c:expr) => {
        $crate::Constraint::lt($crate::Clock::from($x), $crate::Clock::ZERO, $c)
    };
    ($x:ident <= $c:expr) => {
        $crate::Constraint::le($crate::Clock::from($x), $crate::Clock::ZERO, $c)
    };
    // `x > c` is `0 - x < -c`; `-c` overflows only for `i32::MIN`.
    ($x:ident > $c:expr) => {
        match ::core::primitive::i32::checked_neg($c) {
            ::core::option::Option::Some(c) => {
                $crate::Constraint::lt($crate::Clock::ZERO, $crate::Clock::from($x), c)
            }
            ::core::option::Option::None => ::core::result::Result::Err($crate::Error::Range),
        }
    };
    // `x >= c` is `0 - x <= -c`.
    ($x:ident >= $c:expr) => {
        match ::core::primitive::i32::checked_neg($c) {
            ::core::option::Option::Some(c) => {
                $crate::Constraint::le($crate::Clock::ZERO, $crate::Clock::from($x), c)
            }
            ::core::option::Option::None => ::core::result::Result::Err($crate::Error::Range),
        }
    };
}
