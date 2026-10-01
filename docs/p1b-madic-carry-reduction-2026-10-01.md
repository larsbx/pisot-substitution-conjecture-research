# P1b strict zipper: M-adic carry reduction — 2026-10-01

**Status:** repository proof of an exact finite-place reduction and a negative
architectural result for #139. The reduction supplies a sound M-adic
prefilter, but proves that iterating this quotient alone reconstructs the
existing affine overlap recurrence rather than creating a new closure
mechanism. It does **not** prove AdelicPeriodicOffsetHitting, overlap
productivity, or PSC.

## 1. Descaled prefix-difference candidates

For ordered letters (i,j), let

[
D_m(i,j)=P_m(i)-P_m(j)subseteq mathbb Z^3
]

be the difference of proper-prefix Parikh sets.

Define the descaled integral candidate set

[
Z_m(i,j)
 ={zinmathbb Z^3: M^m zin D_m(i,j)}.
	ag{1}
]

This is the part of the level-(m) prefix-difference set that survives the
strongest level-(m) finite cokernel

[
mathbb Z^3/M^mmathbb Z^3,
]

followed by exact integral descaling.

For an overlap offset (w), the existing boundary-hitting criterion becomes

[
M^m win D_m(i,j)
quadLongleftrightarrowquad
win Z_m(i,j).
	ag{2}
]

Thus the strict-zipper target is exactly eventual membership of its realized
offset in these descaled candidate sets.

## 2. Finite-place zero-class lemma

### Lemma 2.1

If an overlap ((i,j,w)) has an offset-zero descendant at level (m), then
some occurrence-labelled (din D_m(i,j)) satisfies

[
din M^mmathbb Z^3.
	ag{3}
]

Equivalently, the corresponding prefix difference is zero in

[
mathbb Z^3/M^mmathbb Z^3.
]

Therefore, if no proper-prefix occurrence pair survives the zero class at
level (m), a level-(m) hit is impossible.

### Proof

A hit gives (d=M^m w) for some (din D_m(i,j)). Since
(winmathbb Z^3), equation (3) follows. ∎

This is one-sided. A zero-class survivor is not a hit: it has the form
(d=M^m z) for a unique integral (z), and the hit occurs only when
(z=w).

For unimodular (M), (M^mmathbb Z^3=mathbb Z^3), so every prefix
difference survives. The filter correctly contributes no information in the
unit case.

## 3. Exact carry recursion

### Theorem 3.1 — descaled candidates obey the overlap affine update

For (mge0),

[
zin Z_{m+1}(i,j)
]

if and only if there are occurrences

[
sigma(i)=p,a,s,qquad
sigma(j)=q,b,t
]

and a state (z'in Z_m(a,b)) such that

[
z'=Mz+pi(q)-pi(p).
	ag{4}
]

The occurrences are part of the witness; repeated child letters at different
positions are not identified.

### Proof

A proper prefix of (sigma^{m+1}(i)) that enters the occurrence
(sigma^m(a)) after the first-level prefix (p) has Parikh vector

[
M^mpi(p)+u,qquad uin P_m(a).
]

Similarly the bottom prefix has the form

[
M^mpi(q)+v,qquad vin P_m(b).
]

Their difference is

[
d_{m+1}
 =M^m(pi(p)-pi(q))+(u-v).
	ag{5}
]

Now (zin Z_{m+1}(i,j)) precisely when
(d_{m+1}=M^{m+1}z) for some such occurrence pair. Rearranging (5),

[
u-v
 =M^migl(Mz+pi(q)-pi(p)igr).
]

Hence

[
z':=Mz+pi(q)-pi(p)in Z_m(a,b),
]

which is (4). Every step reverses, so the condition is also sufficient. ∎

## 4. The key architectural consequence

Equation (4) is exactly the occurrence-labelled overlap child recurrence

[
w'=Mw+pi(q)-pi(p).
	ag{6}
]

Therefore the family (Z_m) is not a new dynamical state space. It is the
**reverse zero-offset basin of the same affine overlap dynamics**:

[
win Z_m(i,j)
quadLongleftrightarrowquad
(i,j,w)	ext{ has an occurrence-labelled length-}m
	ext{ path to offset zero}.
	ag{7}
]

This is the important negative result:

> **Deeper M-adic quotienting by itself cannot close #139.** Once a zero-class
> prefix difference is integrally descaled, its carry recursion is precisely
> the affine overlap recurrence already present in the strict-zipper graph.

The finite-place quotient is still useful computationally because it can
discard impossible prefix pairs before exact comparison. But no iteration of
that same divisibility filter can manufacture the missing recurrence/coverage
theorem.

The next universal step must therefore add information not contained in the
affine graph alone: occurrence-compatible Rauzy-subtile geometry,
Archimedean-plus-finite-place coverage, or another complete recurrence theorem.

## 5. Canonical exact diagnostic

Canonical Mojo support is in

- mojo/psc/overlap_madic_filter.mojo;
- mojo/tests/test_overlap_madic_filter.mojo.

The diagnostic enumerates occurrence-labelled proper-prefix pairs and retains
only differences in (M^mmathbb Z^3), using the exact M-adic lattice carrier
from finite_linear_algebra. A configured word cap raises and is never
reported as a negative result.

On the determinant-two golden regression

    0 -> 1
    1 -> 0 2 1
    2 -> 0 0 1

the ordered pair ((1,2)) at level two has word lengths (7) and (5),
hence (35) proper-prefix occurrence pairs. Exactly (11) survive the
zero class in (mathbb Z^3/M^2mathbb Z^3).

This is an exact finite-domain fact and demonstrates that the non-unit
finite-place filter is nontrivial.

On the unimodular Tribonacci substitution

    0 -> 0 1
    1 -> 0 2
    2 -> 0

the level-two pair ((0,1)) has (12) proper-prefix occurrence pairs and
all (12) survive, as required because the cokernel is trivial.

The diagnostic explicitly exports the non-claim that a zero-class survivor
proves a hit.

## 6. Relation to the adelic target

The M-adic quotient is a conservative integral shadow of the finite-place
coordinates required in the non-unit representation. It does **not** replace
the full Minervino–Thuswaldner representation and is not called a local-field
model.

The current strict-zipper route can now be separated into three layers:

1. **finite-place compatibility:** the prefix difference survives
   (mathbb Z^3/M^mmathbb Z^3);
2. **integral carry state:** descaling gives (zin Z_m(i,j)), whose recursion
   is exactly the overlap affine update;
3. **new geometric forcing:** prove that a realized periodic strict-zipper
   offset must enter this reverse zero basin.

Layers 1–2 are now exact. Layer 3 is AdelicPeriodicOffsetHitting and remains
open.

## 7. Next admissible theorem

The next proof should not be “use a deeper cokernel.” The exact recurrence
above shows that this only refines the same affine carry information.

The next admissible target is:

> **Occurrence-compatible adelic coverage lemma (open).** For a child-closed
> realized strict-zipper SCC, the full adelic periodic orbit of at least one
> vertex must enter the graph-directed prefix-difference subtile corresponding
> to its occurrence-labelled reverse zero basin.

A weaker theorem about closure, positive measure, multiple tiling, or an
untyped difference of Rauzy subtiles remains insufficient.

## 8. Generality firewall

No inverse of (M) over (mathbb Z^3) is assumed. No unimodularity,
Euclidean-only internal space, global realization, legality of the swap word,
or finite-search completeness assumption is introduced.
