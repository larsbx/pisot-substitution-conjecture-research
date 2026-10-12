# K2 load-bearing SCC salvage note (2026-10-11)

**Status:** research salvage / audit note. This document changes no theorem,
ledger or manuscript status. It extracts the useful parts of the October 11
`K_2`/balanced-pair discussion and records the failed finite-closure step so it
is not reused.

## Executive summary

The useful result is a conditional load-bearing SCC theorem:

> If the balanced-pair closure reachable from a length-two dominant `K2`
> source is finite, then some recurrent SCC in that closure has transition
> spectral radius at least `beta * |beta_2|`.

The unconditional finite-closure claim is **not** proved here. In particular,
the predecessor-contraction argument

```text
beta * L(s') <= L(s) + D
```

for a child `s` of `sigma(s')` is invalid for the full balanced-pair closure:
`sigma(s')` may split into many balanced children, and one short child does not
control the total Perron length of the parent.

This note is therefore useful only as a conditional theorem package and as a
warning against the failed contraction route.

## Salvaged definitions

Work on alphabet `{1,2,3}`. Let `M` be the incidence matrix of a primitive
irreducible Pisot substitution, with Perron eigenvalue `beta` and second
conjugate modulus `|beta_2|`. Let

```text
Phi_2 = Lambda^2 M.
```

For balanced pairs, use the standard length-two sources

```text
s_12 = ((1,2),(2,1))
s_13 = ((1,3),(3,1))
s_23 = ((2,3),(3,2)).
```

Their `K2` vectors are, up to sign convention, the standard basis vectors of
`Lambda^2 Z^3`:

```text
e_12, e_13, e_23.
```

## Lemma A: dominant length-two K2 source

At least one of `s_12`, `s_13`, `s_23` has nonzero projection onto the dominant
`Phi_2` eigenspace.

Reason: the three `K2` vectors span `Lambda^2 R^3`. The dominant spectral
projection of `Phi_2` is nonzero, so it cannot vanish on every basis vector.
Equivalently, if every length-two source projected trivially to the dominant
subspace, the dominant projection would be the zero map.

This is the cleanest usable part of the session: it avoids all length-seven
seed machinery for the Case-A / `K2 != 0` lower-bound source.

## Lemma B: K2 additivity over balanced decomposition

If a balanced pair decomposes at Parikh contacts into balanced subpairs

```text
(u,v) = disjoint union_k (u_k, v_k),
```

then

```text
K2(u,v) = sum_k K2(u_k,v_k).
```

The cross-block terms cancel. For each ordered pair count `N_ab`, writing
`u = u_1 ... u_m` gives within-block terms plus cross-block terms
`N_a(u_k) N_b(u_l)` for `k < l`. Since every block pair `(u_k,v_k)` is balanced,
`N_a(u_k) = N_a(v_k)` for every letter `a`, so all cross-block differences
cancel.

This closes the earlier apparent `K2` decomposition gap. No false intertwining
claim is needed: we do **not** assert `K2 ∘ N = Phi_2 ∘ K2` at the transition
matrix level.

## Conditional theorem: load-bearing SCC under finite closure

Assume the balanced-pair closure `B_sigma(s_0)` reachable from a dominant
length-two source `s_0` is finite. Let `N` be the transition matrix on this
finite reachable graph. Then

```text
rho(N) >= beta * |beta_2|.
```

Consequently, by SCC condensation, some recurrent SCC `C` satisfies

```text
rho(N_C) >= beta * |beta_2|.
```

### Proof sketch

1. Choose a length-two source `s_0` with nonzero dominant `K2` projection.
2. Whole-pair substitution gives exact growth:

   ```text
   K2(sigma^k s_0) = (Lambda^2 M)^k K2(s_0).
   ```

3. Therefore `||K2(sigma^k s_0)||` grows at exponential rate
   `beta * |beta_2|`.
4. Balanced decomposition additivity gives

   ```text
   K2(sigma^k s_0) = sum_{c in D_k} K2(c),
   ```

   where `D_k` is the multiset of depth-`k` decomposed descendants.
5. Hence

   ```text
   sum_{c in D_k} ||K2(c)|| >= const * (beta * |beta_2|)^k.
   ```

6. Finite closure gives a uniform bound `M* = max_{c in B_sigma(s_0)} ||K2(c)||`.
7. Thus the path count `|D_k|` grows at rate at least `beta * |beta_2|`.
8. Perron-Frobenius for the finite transition matrix gives

   ```text
   rho(N) >= beta * |beta_2|.
   ```

9. The spectrum of a finite directed graph transition matrix is the union of
   SCC block spectra after condensation ordering, so some recurrent SCC attains
   the same lower bound.

## What is not proved

The finite reachable closure hypothesis is not discharged. In particular:

- This note does **not** prove general BPA termination.
- This note does **not** prove finite closure of `B_sigma(s_0)`.
- This note does **not** prove PSC.
- This note does **not** revive the discarded strict-length or no-Case-B-SCC
  routes.

## Retired proof pattern: predecessor contraction

Do not reuse the following pattern as a global closure proof:

```text
If s is a child of sigma(s'), then beta * L(s') <= L(s) + D.
```

It is only plausible for a selected core-child chain where the chosen child
captures essentially all relevant mass. In the full balanced-pair graph, a
parent can have many children, and a single short child gives no upper bound on
parent length.

Any older draft or note relying on this inequality for global finite closure
should be marked conditional or conjectural until replaced.

## Useful next targets

1. Prove finite reachable closure from one dominant length-two source, or find a
   weaker bounded-`K2` substitute sufficient for Step 6 above.
2. Develop a truncation/limiting version of the path-counting proof that avoids
   finite closure.
3. Keep the `K2` additivity lemma as a local theorem: it is independent of the
   finite-closure problem and may simplify future bounded-domain certificates.
