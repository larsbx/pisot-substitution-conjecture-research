# C4 degree-2 three-state trace diagnostic

**Status:** exact necessary-condition identities proved; exhaustive 4,554-PIP corpus calibration complete. The trace conditions are useful filters but are **not** a three-state exclusion theorem.

## 1. Setup

Let `C` be a hypothetical strict closed nonproductive degree-2 SCC with exactly three states. The previously proved intertwiners give

`N_C ~ M_sigma`

and

`S_C ~ Lambda^2 M_sigma`,

because both the Parikh matrix `P_C` and the degree-2 defect matrix `Q_2` are then invertible over `Q`.

Write the positive/negative orientation occurrence matrices as

`A >= 0`, `B >= 0`,

so

`N=A+B`, `S=A-B`.

## 2. Power-trace inequalities

For every integer `k>=1`, expand the noncommutative powers:

`(A+B)^k - (A-B)^k`.

Terms containing an even number of `B` factors cancel; terms containing an odd number double. Hence

`tr(N^k)-tr(S^k) = 2 sum tr(W)`,

where the sum ranges over length-`k` words `W` in `A,B` with an odd number of `B` factors.

Every such matrix product has nonnegative entries because `A,B` are nonnegative, so its trace is nonnegative. Therefore

> `tr(M^k) >= tr((Lambda^2 M)^k)` for every `k>=1`.

For `k=1`,

`T-U = 2 tr(B) >= 0`,

where

`chi_M(t)=t^3-T t^2+U t-d`.

For `k=2`,

`tr(N^2)-tr(S^2)=4 tr(A B)`,

so the trace difference is both nonnegative and divisible by four.

The power sums are computed from the two cubics:

`chi_M(t)=t^3-T t^2+U t-d`,

`chi_Lambda2(t)=t^3-U t^2+d T t-d^2`.

## 3. Exact finite-corpus result

`mojo/degree2_three_state_census.mojo` evaluates these conditions exactly on the established 4,554 alphabet-3 PIP substitutions with image lengths `<=3`.

After first applying the merged mod-2 three-state parity sieve:

- PIP specimens: `4554`;
- three-state parity survivors: `1716`;
- survive trace conditions through `k=1`: `1716`;
- survive through `k=2` plus the mod-4 requirement: `1716`;
- survive through `k=3`: `1662`;
- survive through `k=6`: `1662`;
- survive through `k=12`: `1554`.

First failures occur only at:

- `k=3`: `54` specimens;
- `k=7`: `108` specimens.

An explicit survivor has

`(T,U,d)=(1,-1,1)`,

the Tribonacci characteristic cubic

`t^3-t^2-t-1`.

Thus the trace inequalities remove some parity-admissible cubics, but leave the overwhelming majority.

## 4. Unimodular simplification

For `d=1`, the `k=2` trace difference simplifies to

`D_2=(T-U)(T+U+2)`.

Once the three-state parity condition and `T>=U` hold, the `k=2` condition is typically automatic; in particular it cannot serve as a general unimodular eliminator.

This explains why the exact census gains nothing at `k=2` beyond the parity sieve.

## 5. Consequence for the proof program

The power-trace route is retained as a **necessary arithmetic filter**, not promoted to a proof spine.

A general three-state degree-2 obstruction must use information absent from the spectra of `N` and `S` alone. The missing data is word realization: the ordered signed child substitution must arise from actual irreducible balanced word pairs compatible with `sigma`, not merely from two integer matrices with the correct characteristic polynomials.

The next diagnostic is therefore to construct an explicit synthetic signed three-state template satisfying all currently used matrix/orientation/parity constraints. If such a template exists, it proves decisively that the remaining theorem must distinguish abstract signed substitutions from realizable balanced-pair substitutions.

## 6. Guardrails

- The 4,554 census is finite evidence only.
- Trace positivity is proved as a necessary condition for a three-state strict component, but not sufficient.
- No claim of C4, C1, G1, or PSC is made.
