# Algorithms and implementation

This page describes the implementation of `clock-dbm`: representation,
algorithms, optimizations, and time complexity. The public API pages specify
the mathematical meaning, arguments, results, and errors of each operation.

Let `d = n + 1` be the matrix dimension for `n` actual clocks, including
the reference clock at index 0. All complexity bounds below use `d`.

For general DBM algorithms and operations not detailed here, see
[Bengtsson and Yi (2004), *Timed Automata: Semantics, Algorithms and
Tools*](https://doi.org/10.1007/978-3-540-27755-2_3).

## Storage and working matrices

A nonempty `Dbm` holds a flat, row-major `d × d` array of packed `i32`
bounds. Each finite strict bound `< c` is encoded by `2c`, each weak bound
`<= c` by `2c + 1`, and infinity by a distinguished code. Comparing packed
codes therefore also compares their tightness.

An empty zone retains its clock count but has no stored matrix. Mutations use
a crate-private working matrix, which may temporarily be noncanonical.
The working matrix is published as a `Dbm` only after its canonicality
has been established, or discarded on an error. See [`Dbm`](crate::Dbm)
for the public canonical-or-empty invariant.

## Full closure

Full closure uses Floyd–Warshall. After tightening the diagonal and enforcing
the reference-row nonnegativity constraints, each pivot `k` relaxes entries
using

```text
D[i][j] := min(D[i][j], D[i][k] + D[k][j]).
```

The implementation skips infinite summands and can omit row `k` when its
diagonal is `<= 0`. It checks diagonals for a negative cycle as it proceeds,
and stops if an exact finite intermediate sum cannot be represented.

The worst-case cost is `O(d³)` time and `O(d²)` matrix storage. The
row-major layout permits contiguous, vectorizable inner-row operations.

## Constraint insertion

For a guard `x_i - x_j ⋈ b`, let `u ≼ v` mean that the difference bound
`u` is at least as tight as `v`, and let `u ⊕ v` be exact bound addition:
finite constants add, the sum is strict if either summand is strict, and
infinity is absorbing. These operations are mathematical; a finite
result may be outside the range of the packed `i32` representation.

The input `D` is nonempty and canonical: its diagonals are `Le 0` and
it satisfies the triangle inequalities
`D[k][l] ≼ D[k][i] ⊕ D[i][l]` for all clocks. When adding one
constraint, the implementation distinguishes three cases:

1. **Already implied:** if `D[i][j] ≼ b`, return the original matrix
   unchanged
2. **Immediate contradiction:** if `b ⊕ D[j][i] ≺ Le 0`, the new edge
   creates a negative cycle (including a strict-zero cycle); return empty
3. **Consistent tightening:** otherwise the exact canonical result is

   ```text
   D'[k][l] = min(D[k][l], D[k][i] ⊕ b ⊕ D[j][l]).
   ```

   Any newly shorter path can use the tightened edge only once; the
   original `D` already contains all shortest paths without that edge.
   Evaluating this formula for every `(k, l)` gives an `O(d²)` method.

### Two-phase incremental closure

The consistent-tightening formula can be factored into row updates. First
compute the final row `i`:

```text
D'[i][l] = min(D[i][l], b ⊕ D[j][l]).
```

For any other row `k`, use that updated row:

```text
D'[k][l] = min(D[k][l], D[k][i] ⊕ D'[i][l]).
```

This gives the same result as the one-edge formula. Indeed,
`D[k][l] ≼ D[k][i] ⊕ D[i][l]` by canonicality, so the part of
`D'[i][l]` inherited from the old row `i` cannot improve row `k`.
Only a path containing the new edge can improve it.

The computation can be performed in place: since
`b ⊕ D[j][i] ≽ Le 0`, the one-edge formula leaves column `i` and
row `j` unchanged. Thus the values required by the second phase are
not overwritten by the first.

### Skipping rows that cannot change

Before updating row `k ≠ i`, first inspect the single candidate
`D[k][i] ⊕ b` for entry `(k, j)`. **Skip the entire row** when

```text
D[k][i] ⊕ b ≽ D[k][j].
```

To see why, for every column `l` the comparison implies

```text
D[k][i] ⊕ b ⊕ D[j][l]
    ≽ D[k][j] ⊕ D[j][l]
    ≽ D[k][l].
```

The last inequality is the triangle inequality of the original
canonical matrix. Hence, the new edge cannot improve **any** entry in
row `k`. Conversely, if the comparison fails, column `j` itself
tightens, since `D[j][j] = Le 0`, so this row needs processing.
If `D[k][i]` is infinite, the candidate path is infinite and the
row can also be skipped.

The resulting implementation strategy is:

1. Handle implied and inconsistent constraints before modifying storage.
2. Compute row `i` using the first-phase formula.
3. For each remaining row `k`, check the candidate for column `j`.
   Skip the row unless it strictly tightens that entry.
4. For each non-skipped row, use the **updated** row `i` and the
   original `D[k][i]` to apply the second-phase formula to all columns.
5. Publish the result only after successful completion.

This costs `O(d)` for the row checks plus `O(d)` for each row that needs
relaxation, at most `O(d²)`. The whole-row updates are implemented with
a contiguous, vectorizable primitive; there is no full
Floyd–Warshall pass or backup matrix on the successful path.

For one actual clock (`d = 2`), a consistent tightening changes only
entry `(i, j)`; the implementation handles this with a single store.

For a batch, `try_constrain_all` validates indices, checks individual
contradictions, and chooses a strategy using a threshold of `4d` guards:
small batches use repeated incremental insertion, while larger batches
tighten the relevant entries followed by one full closure. The `Workspace`
parameter is not currently needed by the batch implementation.

## Temporal operations

These operations require no full closure. Except for `past`, they update
`O(d)` entries of a canonical matrix:

| Operation | Matrix update |
|---|---|
| `future` | Set column 0 to infinity except for the diagonal |
| `past` | Set row 0 to `min(Le 0, D[1][j], …, D[n][j])` column by column; every other entry stays |
| `try_reset_zero(x)`, `try_reset(x, c)` | Derive row and column `x` from the reference row and column, shifted by `c` and `−c` |
| `try_free(x)` | Copy column 0 to column `x`, set row `x` to infinity, then restore its diagonal |

`past` keeps every upper bound and every difference between actual clocks,
because a common delay changes neither. It cannot simply set the lower
bounds to `Le 0`. That would be sound but not canonical: `x − y ≥ 5` and
`y ≥ 0` still imply `x ≥ 5`. Because the input is closed, the one-step path
`0 → i → j` already gives the tightest bound. So the implementation fills
row 0 with `Le 0` and then takes one vectorized row minimum with each row
`i ≥ 1`, in place. This takes `O(d²)` time, cannot overflow, and needs no
closure.

Reset updates the row before the column, so the second pass reads a
reference-column value established by the first. These whole-row/column
updates preserve canonicality, allowing publication without an additional
closure.

## Intersection and queries

`try_intersect` first takes the entrywise minimum of the input matrices
and marks both endpoint clocks of every changed entry. It then uses
Floyd–Warshall relaxation **only over those marked clocks as pivots**.
With `p` marked clocks, its cost is `O(d² + p·d²)`, bounded by `O(d³)`.

Because inputs are canonical, query operations can avoid closure:

| Operation | Implementation | Time |
|---|---|---|
| `is_subset_of` | Compare the stored bounds entrywise | `O(d²)` |
| `entails` | Check the queried canonical entry against the bound | `O(1)` |
| `intersects_constraint` | Check the queried edge against the opposite entry for a negative cycle | `O(1)` |
| `difference_bound` | Read the corresponding canonical entry | `O(1)` |

None of these query paths allocates a new matrix.

## Maximal-constant extrapolation (ExtraM)

`try_extrapolate_max` applies the entrywise normalization specified by
its [API documentation](crate::Dbm::try_extrapolate_max). Normalization
takes `O(d²)` time. When no entry changes, the input is already canonical
and closure is skipped. Otherwise normalization may have invalidated
triangle inequalities, so the implementation runs full closure over
**all** pivots, taking `O(d³)` time in the worst case.

This is the implemented ExtraM strategy; other abstraction algorithms are
not part of the implementation.

## Shared storage and workspace

`SharedDbm` uses `Rc<Dbm>`. Cloning a handle increments a non-atomic
reference count instead of copying a matrix. A consuming update can use
`Rc::get_mut` for unique storage, or clone the matrix before modification
when multiple handles share it.

Several fast paths avoid that copy: implied or contradictory constraints,
empty operands, and certain already-contained intersections are recognized
before detaching. These checks are worthwhile when they avoid copying
`O(d²)` matrix entries.

`Workspace` reuses an internal vector of pivot flags, especially for
intersection and ExtraM. Its mutable borrow lasts only for the operation.
The current `Workspace::with_capacity` is a sizing hint and does not
preallocate the vector.

