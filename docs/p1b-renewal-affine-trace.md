# P1-B — affine prefix-suffix trace diagnostic

**Status:** exact symbolic diagnostic for the open G1b-2 renewal-finiteness gate. This construction does **not** prove renewal finiteness, identify every symbolic pump with one physical renewal state, or establish that order-sensitive data are necessary.

## 1. Motivation

The sidewise finite-cokernel experiment for

```text
0 -> 1
1 -> 021
2 -> 001
```

with the single strict first-return seed `(01,10)` leaves one residual bounded-projection collision after the tested abelian refinements:

```text
depth 7, cut 14
versus
depth 5, cut 14.
```

Both observations have the same tested exact sidewise prefix translations

```text
p_top    = (5,6,3)
p_bottom = (5,6,3),
```

so further quotienting of those same abelian translations cannot distinguish them. This motivates testing a coordinate that retains the **ordered prefix-suffix path** rather than only its accumulated Parikh translation.

## 2. Affine trace

For one paired ancestry edge at level `t`, let

```text
q_t = Parikh(proper prefix before the top child)
    - Parikh(proper prefix before the bottom child).
```

Starting from the source prefix defect `delta`, evolve

```text
x_0     = delta,
x_{t+1} = M x_t + q_t.
```

The exact trace state at a boundary between ancestry levels is

```text
(top_current_letter, bottom_current_letter, x_t).
```

For a certified depth-`d` renewal address, the terminal residual satisfies

```text
x_d = 0.
```

The implementation checks parent/child continuity at every edge and fails closed unless the terminal state closes exactly.

## 3. Proper internal repeated states

Suppose one exact state repeats at boundaries

```text
0 < i < j < d.
```

Then the paired edge block `i,...,j-1` begins and ends at the same two current letters and at the same affine residual. Deleting that block therefore gives a valid symbolic splice and leaves the subsequent affine evolution unchanged.

The implementation deliberately excludes repeats involving the initial or terminal boundary. A start/terminal repeat can occur simply because the whole certified address is a closed affine path; deleting the entire path would collapse an interior renewal cut to a depth-zero boundary and is not justified as a physical renewal equivalence.

After a proposed internal deletion, the shortened path is re-parsed and its terminal residual is rechecked exactly. This certifies only the shortened **symbolic affine path**. No physical realization claim is made unless an independently certified observation has exactly that shortened path.

## 4. Canonical survivor regression

For the unique residual pair from the finite-cokernel experiment, the depth-7 affine trace has the same exact state at boundaries `1` and `3`:

```text
(top letter, bottom letter, residual) = (1, 0, (0,0,0)).
```

Deleting ancestry edges `1` and `2` from the depth-7 symbolic path yields a depth-5 path. The resulting path agrees **exactly** with the independently certified depth-5/cut-14 address.

The certified depth-5 address has no proper internal repeated affine state. Its initial and terminal states agree, but that boundary repeat is excluded from pump deletion by construction.

This is an exact finite-corpus normalization result for this witness, not a general pumping theorem.

## 5. Previously observed right-edge recurrence

The regular right-edge family identified before the cokernel experiment is also recovered by the affine trace. At depth 4, the three right-edge cuts have an internal repeated state at boundaries `1` and `2`. Deleting that one-edge loop produces the exact independently certified depth-3 address at the corresponding right-edge cut.

Thus the affine trace subsumes both tested recurrence mechanisms:

- the earlier one-edge synchronous `(1,2)` self-loop; and
- the two-edge cycle hidden from the simple synchronous-insertion quotient in the depth-7/cut-14 survivor.

## 6. What this establishes and what it does not

The finite evidence establishes that the tested affine state can recognize and safely splice two concrete recurrence families while retaining edge order.

It does **not** establish:

- that every long realizable renewal address contains a proper repeated affine state;
- that every symbolic affine splice corresponds to the same physical reduced balanced pair;
- that the set of affine states is uniformly finite under bounded discrepancy;
- that other finite commutative refinements cannot work;
- or G1b-2.

The theorem-facing next question is whether realizability plus the standing bounded-discrepancy input gives a uniform bound/finite set for the exact affine states that can occur before the terminal zero. If not, the retained counterexamples should determine which additional finite coordinate is missing. G1b-2 remains open.
