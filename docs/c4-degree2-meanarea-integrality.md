# C4 degree-2 three-state mean-area integrality sieve

**Status:** exact algebraic consequence of the order-sensitive mid-area identity. It gives a finite necessary realizability test for an ordered three-state candidate. It does **not** prove C4, C1, G1, or PSC.

## 1. From mid-area to mean-area

For a balanced state `T=(u,v)`, the mid-area

`H(T)=area(u)+area(v)`

is always even. Indeed

`area(u)-area(v)=2 K2(T)`,

so

`H(T)=2(area(v)+K2(T))`.

Define the integer **mean-area** column

`J(T)=H(T)/2`.

For a candidate ordered child substitution `tau`, the mid-area identity becomes

> `
> (Lambda^2 M) J - J N = Omega_tau - C_sigma P.
> `

Here:

- `N` is the unsigned child-incidence matrix;
- `P` contains the common Parikh columns;
- `C_sigma[:,a]=area(sigma(a))`;
- `Omega_tau[:,T]=sum_{r<s}p(R_r) wedge p(R_s)` for the **ordered** child word of `T`.

All terms on the right are integer data.

## 2. Why the three-state solution is unique

For `|C|=3`, the Parikh intertwiner gives

`N=P^{-1} M P`,

so `N` and `M` have the same irreducible cubic spectrum.

The exterior-square eigenvalues are the pairwise products of the eigenvalues of `M`. Suppose an eigenvalue `lambda_i` of `M` were also an eigenvalue of `Lambda^2 M`. Then for some complementary pair,

`lambda_i=lambda_j lambda_k=d/lambda_i`,

hence

`lambda_i^2=d in Q`.

But an eigenvalue of an irreducible cubic has degree three over `Q`, contradiction.

Therefore `spec(M)` and `spec(Lambda^2 M)` are disjoint. The Sylvester operator

`X -> (Lambda^2 M)X-XN`

is invertible over `Q`.

Thus **every ordered three-state candidate forces one unique rational matrix `J`**.

Actual balanced-word realization requires at least:

1. `J` is integral;
2. the side-area columns `J+Q` and `J-Q` satisfy the elementary Parikh parity and magnitude bounds for word areas.

These are finite exact tests before any full word equation is solved.

## 3. Resultant of the Sylvester operator

Write

`chi_M(x)=x^3-Tx^2+Ux-d`.

Then

`chi_Lambda2(x)=x^3-Ux^2+dT x-d^2`.

The determinant of the `9x9` Sylvester linear operator is the resultant

```text
-d^2 (T-U+d-1)^2
  (-T^2 d - 2 T d + U^2 + 2 U d + d^2 - d).
```

For an irreducible cubic with `d!=0`, this is nonzero by the disjoint-spectrum argument above.

The explicit factorization matters arithmetically: primes dividing this resultant are the only possible denominator primes in the forced rational mean-area solution. This provides a route to congruence obstructions stronger than the already-merged mod-2 characteristic-polynomial sieve.

## 4. Strong G/F synthetic calibration

For the actual PIP substitution

```text
1 -> 2
2 -> 3
3 -> 132
```

and the three synthetic balanced states from the companion obstruction, the proposed ordered child words are

```text
T0 -> T1
T1 -> T2
T2 -> T0 T1 T2
```

when orientation signs are forgotten.

The unique rational solution forced by the mean-area equation is

```text
J = [ 1/2 -1/2  3/2]
    [ 3/2  1/2  3/2]
    [ 1/2  1/2 -5/2].
```

It is not integral. Therefore **no choice of actual balanced side words with those fixed `P,Q` columns can realize this ordered child substitution**.

The Sylvester determinant is `-16`, matching the closed resultant formula exactly.

This is a stronger rejection than comparing the chosen synthetic words directly: the proposed ordered child system is impossible for the entire Parikh/`K2` column data, regardless of how one tries to replace the individual state words.

## 5. Side-area feasibility after integrality

If `J` is integral, the two side-area vectors of state `T_j` must be

`a(u_j)=J_j+Q_j`,

`a(v_j)=J_j-Q_j`.

For Parikh vector `p=(n1,n2,n3)`, any word area `a=(a12,a13,a23)` satisfies coordinatewise

`|a_ij| <= n_i n_j`

and

`a_ij == n_i n_j (mod 2)`,

because

`N_ij+N_ji=n_i n_j`,

`a_ij=N_ij-N_ji`.

The implementation checks these necessary bounds automatically.

## 6. Research consequence

For a three-state strict degree-2 candidate, the ordered child words are no longer free combinatorial decorations. Once `sigma`, `P`, and `tau` are fixed, their cross-wedge data `Omega_tau` determines the only possible mean-area matrix.

This suggests a finite elimination program:

1. enumerate the finitely many child orders compatible with a candidate `N` and endpoint first/last selectors;
2. solve the Sylvester equation exactly for each order;
3. reject nonintegral `J`;
4. reject side-area parity/bound violations;
5. only then attempt full balanced-word realization.

The exact 4,554-PIP census already shows that no arithmetic+endpoint survivor realizes an actual recurrent size-three SCC. Mean-area integrality is a concrete candidate for explaining a substantial part of that finite gap and, potentially, for proving the general three-state exclusion.

## 7. Executable scope

`src/psc_research/meanarea_integrality.py` provides:

- ordered child incidence and cross-area matrices;
- the exact `9x9` Sylvester operator;
- Fraction-exact solution for the forced mean-area matrix;
- integrality and side-area feasibility tests;
- the closed cubic resultant formula;
- an exact fraction-free determinant cross-check.

`tests/test_meanarea_integrality.py` pins the half-integral G/F synthetic obstruction and the resultant value `-16`.
