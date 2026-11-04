# C4: positive frequency of genuine physical hub crossings in a hypothetical strict flat component

**Status:** proposed parameter-uniform, **conditional** quantitative lemma under the
supplied, fully strict child-closed Pisot component and common orientation sign
of merged [PR #465](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/465).
No such component is asserted to exist. This does **not** establish a
synchronizing newborn, C4, G1, BH, A1′ or PSC. Existing physical crossing work
in [PR #466](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/466)
addresses genuine overlap versus coincident symbolic indices; that PR is a
separate dependency and its eventual hosted acceptance must be inspected.

## Stop/go and mathematical target

The [hub-prefix crossing lemma](c4-hub-prefix-crossing-2026-11-04.md)
already proves a **positive asymptotic fraction of synchronous-index
prefix-negative factors**, using the exterior-square defect and Perron
growth. But its negative index event need not be a physical overlap:
PR #466 exhibits an equal-index crossing whose source intervals are
separated, alongside a distinct physical overlap which is productive.

The new target is a stronger quantitative assertion for **physical**
events, without treating an endpoint order as a good-edge transfer.
Rather than convert synchronous indices to physical positions, use the
same degree-two defect with arbitrary weighted *physical completion
areas*. This is a standard elementary linear-algebra/conservation
argument; no new spectral criterion or novel source theorem is claimed.

## Definitions and theorem

Fix a primitive irreducible ternary Pisot substitution sigma, incidence
matrix M, Perron root beta>1, and **positive** left Perron vector
ell=(ell_0,ell_1,ell_2) with ell M=beta ell.
Let C be a supplied **nonempty finite, strongly connected, complete
strict child-closed** family of irreducible noncoincident balanced word
pairs. Choose a hub h so that after orienting every member (u,v), its
top word starts with h and its bottom word starts with a different
letter. Require that **every actual ordered child occurrence** in
every full factorization has the *same* orientation sign s=+1 or s=-1,
relative to these chosen hub orientations. Retain all occurrences,
including multiplicities. These are exactly the strong conditions
needed by #465; a merely recurrent subset with escaping children is
not eligible.

For a hub-oriented balanced pair T=(u,v), lay both words over
[0,L_T] using the **same** lengths ell. Define

    H_T(x) = #completed top h tiles at or before x
             - #completed bottom h tiles at or before x,

and its physical signed area

    A_T = integral_(0 to L_T) H_T(x) dx.

Call T *physically crossing* when H_T(x)<0 on a nonempty open
interval. This is a **geometric** definition, not a comparison of
symbolic positions or an asserted synchronizing newborn.

Let ell_min=min_a ell_a>0, let B=max_(T in C)|A_T|, and let c_n be
the number (with occurrence multiplicity) of physically crossing
factors in the **complete** ordered factorization of
sigma^n(T_0), for any root T_0 in C. Let r_n be the total number of
factors at that depth.

> **Conditional physical crossing-frequency theorem.**
> Under the hypotheses above,
>
>     liminf_(n->infty) c_n/r_n >= ell_min/(ell_min+B) > 0.
>
> More precisely, with 0<rho<beta a valid spectral bound for
> Λ²M, there is a finite root-dependent constant C_0 such that
>
>     c_n/r_n >= [ell_min - C_0 (rho/beta)^n] / (ell_min+B)
>
> for all n. For an actual finite C the positive lower fraction
> is explicit in its finitely many areas and the positive Perron
> lengths. It is a density of **occurrence factors**, not of
> distinct vertices and not necessarily a density of Sync newborns.

### Proof

**1. Exact area identity.** For every balanced T and every positive
letter-width vector w, let K_hx(T) be the top-minus-bottom
difference of scattered subword counts hx. Integrate the completed-h
count across each x tile. Each earlier h contributes precisely
w_x to the integral. The two words have equal Parikh mass and
therefore equal physical total length. Their hub/hub contributions
cancel. Thus

    A_w(T) = sum_x w_x K_hx(T).

This is an exact finite word identity, independent of Pisot arithmetic.

**2. Uniform strictly positive area of a noncrossing factor.**
The top begins with h and the bottom begins with a nonhub letter b.
The top's first hub finishes at time ell_h. The earliest the bottom
can complete any h is time ell_b+ell_h, because its first tile is
b != h and every h tile has the same width ell_h. Balanced total
mass ensures the common word has length at least ell_b+ell_h.
Consequently H_T(x)>=1 throughout the interval
(ell_h,ell_h+ell_b). If H_T never becomes negative, its area
A_T is at least ell_b>=ell_min. For a crossing factor,
A_T>=-B by definition. Hence, for any complete ordered list of
r factors containing c physical crossings,

    sum_(factors) A_T >= ell_min*(r-c) - B*c.             (1)

**3. Complete word-factorization additivity and the common sign.**
The hub-count difference is zero at both ends of *each balanced
child block*. Hence physical completion areas add over
concatenation, with no offset or cross-term. If a factor is
physically side-swapped relative to its chosen orientation, its
area changes sign. The universal sign s in every actual child
therefore gives, for the complete depth-n factorization,

    sum_(factors) A_T = s^n * A_ell(sigma^n(T_0)).       (2)

In particular selected paths or a recurrent SCC with exits cannot
be substituted for all actual factors in (2).

**4. Spectral smallness of the total signed area.**
For balanced pairs their antisymmetric degree-two scattered
subword vector D satisfies the exact substitution law

    D(sigma^n(T_0)) = (Λ²M)^n D(T_0).

Applying the linear area functional from step 1, every eigenvalue
of Λ²M is a product of two distinct conjugates of M. In the
irreducible Pisot regime all such products have modulus strictly
less than beta. (The cubic roots are distinct in characteristic
zero.) Choose rho between their spectral radius and beta. There
is therefore C_1<infty with

    |A_ell(sigma^n(T_0))| <= C_1 rho^n.                  (3)

**5. Perron lower bound on the factor count.**
Let L_max=max_(T in C) L_T, finite because C is finite. The
inflated root has length beta^n L_(T_0). Every strict child
factor has length at most L_max. Full closure yields

    r_n >= (L_(T_0)/L_max) beta^n.                      (4)

Combine (1)–(4) and divide by r_n:

    c_n/r_n >= (ell_min - C_1 L_max/L_(T_0)
                          *(rho/beta)^n)/(ell_min+B).

Let n tend to infinity. QED.

## Why this does not close C4

Every physically crossing factor carries a genuine overlapping
top-nonhub/bottom-hub source occurrence by the elementary
first-negative-completion argument of #466. The theorem therefore
gives a positive factor *frequency* of such physical overlap
opportunities under the very strong hypothetical strict-flat
component hypotheses.

It does **not** prove any such overlap gives a zero offset,
an eventual diagonal, or the required **one-step interior newborn
Sync_+ or Sync_-**. In particular the productive PIP control
`1/02/220` explicitly has a separated equal-index hub crossing
and a different productive physical crossing. Its recurrent subset
has exits, violating our crucial complete-closure hypothesis.
The reducible strict `10/102/211` control does not satisfy the
Pisot exterior-square spectral gap and has no physical crossing.
The productive `01/12/021` control has a physical negative
interval but is not a closed strict component.

The next useful work is a **whole-word, all-child synchronization
mechanism** that acts on these frequent physical crossing
opportunities while retaining exact positions, both orientations,
legal ancestry and the genuine witnessed good edge. No statement
that frequency alone forces synchronization is authorized.

## Canonical executable and independent oracle

The canonical module `kernel/psc/c4_physical_hub_area.mojo` takes a
balanced actual ternary word pair and an arbitrary **positive
integer** width vector. It merges every physical endpoint exactly,
measures negative/positive completion intervals and compares the
result with the existing degree-two `psc.words.k2` tensor.
It rejects nonpositive widths, unbalanced or malformed words,
incorrect hub orientation and checked-integer overflow. Its
noncrossing initial plateau check is explicit. These integer
widths test the *universal combinatorial area identity*; they do
not approximate or replace the exact Perron vector in the theorem.

`kernel/tests/test_c4_physical_hub_area.mojo` replays the strict
reducible, productive phase-zero and productive phase-one
controls, plus balanced concatenation and malformed inputs.
`tests/test_c4_physical_hub_area_oracle.py` independently
reconstructs the completed-h count at every integer time,
exhaustively compares short balanced pairs and validates the
scattered-subword formula by explicit letter-pair loops.

Reproduce:

```sh
cd kernel
pixi run --locked mojo run -I . tests/test_c4_physical_hub_area.mojo
cd ..
python -m pytest -q tests/test_c4_physical_hub_area_oracle.py
```

**Evidence status:** proof derivation and executable sources supplied;
new native and hosted CI results require exact-head replay. An
independently executed local integer sweep on the fixed controls
reproduced the expected weight-(2,3,5) areas -3, 26 and 5,
with negative lengths 5, 5 and 0 respectively. That is only
finite calibration, not a machine proof of the uniform spectral
theorem. No generated governance or theorem statuses change.
