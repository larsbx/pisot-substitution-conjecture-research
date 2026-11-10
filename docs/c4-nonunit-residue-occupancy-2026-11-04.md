# Non-unit occupancy: an exact residue certificate and its useful consequences

**Status:** written finite-index counting proofs and an exact certificate for
`0 -> 1, 1 -> 021, 2 -> 001`. Independent human mathematical review remains
pending. The finite executables check the residue table, algebra and literal
coincidence witnesses; they do not machine-check the measure arguments.
No general C4, G1, BH, A1', PDS or PSC status is promoted.

## 1. What replaces the scratch observation

[PR #493](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/493)
at `d9f8f0a69d6ae0b311578b255a53f2403d428eee` correctly leaves the old
non-unit occupancy computation as an **unverified scratch observation**.
The old program and any purported exact occupancy values are not used here.
This note establishes its useful qualitative conclusion independently:

> For `1/021/001`, every positive-prefix Euclidean subtile has occupancy
> strictly below one half, although all three letter pairs have explicit
> left strong-coincidence witnesses.

The proof computes **upper bounds**, not the exact occupancies or fractal
areas. Depth two is sufficient. The useful new machinery is a general
finite-residue bound, its monotonicity, and its version for two strict tracks.
The [literature gate](c4-nonunit-residue-occupancy-literature-gate-2026-11-04.md)
was completed before implementation. The
[compact M-adic lift](c4-nonunit-madic-counting-bridge-2026-11-04.md)
then retains all residue levels and derives the corresponding non-unit
counting and overlap statements.

## 2. Definitions and finite-index counting

Let `sigma` be a primitive, irreducible Pisot substitution on three letters,
with column-incidence matrix `M`, Perron eigenvalue `beta > 1`, positive
left length vector `ell`, and positive right frequency vector `f`, normalized
by `sum f_c = 1`. Put `ellbar = ell f` and `D = abs(det M)`.
Choose a one-sided fixed point `w` of a power `sigma^k`. With `pi` the
projection along the Perron line onto the contracting plane, define

```text
R_c = closure { pi p(P) : P c is a prefix of w },
Phi(x) = (ell x, pi x),
kappa = covolume(Phi(Z^3)),
theta_c = kappa f_c / (ellbar lambda(R_c)).
```

The sets `R_c` are compact. One-track counting gives
`lambda(R_c) >= kappa f_c / ellbar > 0`, so `theta_c` is well defined.
It is an area-normalized density ratio; identifying it with the limiting
fraction of all lattice points over the fractal window would additionally
require an appropriate boundary/density statement. We need no such equality.

For a fixed `q >= 0`, put `L_q = M^q Z^3` and `G_q = Z^3/L_q`.
Its order is `D^q`. For `r in G_q`, let

```text
a[c,r,d](q) = #{ sigma^q(d) = P c S : p(P) mod L_q = r },
A[c,r](q)  = sum_d a[c,r,d](q) f_d,
alpha[c,r](q) = beta^(-q) A[c,r](q).
```

Occurrences, including repeated ones, are counted separately. In particular
`sum_r a[c,r,d](q) = (M^q)_{c,d}` and
`sum_r alpha[c,r](q) = f_c`.

### Lemma R1 (fixed-coset density)

For any bounded finite union of boxes `U` with measure-zero boundary and
any fixed coset `r + L_q`,

```text
#{ x in r + L_q : 0 <= ell x < X, pi x in U }
    = X lambda(U)/(kappa D^q) + o(X).
```

Here `q` and `U` are fixed before `X` tends to infinity. The sublattice
`Phi(L_q)` has covolume `kappa D^q`. The physical translation on its
quotient torus has no nonconstant invariant character: such a character
would pull back to a nonzero rational row annihilating the Perron right
eigenvector. No such row exists. Indeed its successive products by `M`
would span a nonzero proper rational invariant subspace, contrary to the
irreducible characteristic polynomial. Hence character averaging gives
unique ergodicity. Apply it to the periodized indicator of `[0,1) x U` at
the coset translate. Its discontinuities have measure zero. Unfolding gives
`lambda(U)/(kappa D^q)`; the two bounded physical endpoint strips change
the count by only `O_U(1)`. This proves the displayed formula.

This is also the regular-window, all-translates clause of
[Moody's Theorem 1](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/2304DD08EC0AD970DEF94D7C180C4752/S0008439500015630a.pdf/div-class-title-uniform-distribution-in-model-sets-div.pdf).
The argument uses regular outer covers, not a density assertion for an
arbitrary fractal boundary.

## 3. The residue upper bound

**Theorem R2 (residue occupancy bound).** For every `c` and `q`,

```text
lambda(R_c) >= (kappa D^q / ellbar) max_r alpha[c,r](q),

theta_c <= U[c,q]
        := f_c / (D^q max_r alpha[c,r](q))
         = beta^q f_c / (D^q max_r A[c,r](q)).                 (1)
```

*Proof.* Let `a` be the initial letter of `w`, so `sigma^(kn)(a)` is an
increasing sequence of prefixes. For `kn >= q`, decompose this prefix as
`sigma^q(sigma^(kn-q)(a))`. The prefix before each `q`-supertile has Parikh
vector in `L_q`. Consequently the number of its `c`-vertices in coset `r`
is exactly

```text
sum_d a[c,r,d](q) (M^(kn-q))_{d,a}.
```

Divide by its physical length `beta^(kn) ell_a` and use Perron--Frobenius.
The limit is `alpha[c,r](q)/ellbar`. Every such vertex projects into `R_c`.
Count the vertices in any regular open box cover of `R_c`, apply the
fixed-coset lemma, then take the infimum of the cover measures. This yields
(1). No recognizability assumption or uniqueness of desubstitution is
needed: the displayed decomposition is a literal word identity. It also
works when `q` is not a multiple of the fixed-point period `k`.

### Corollary R3 (monotonicity and the unit control)

Each coset of `L_q` has exactly `D` children modulo `L_(q+1)`. Counting the
same long prefixes gives the exact compatibility relation

```text
alpha[c,r](q) = sum_{s maps to r} alpha[c,s](q+1).
```

Thus `D^(q+1) max_s alpha[c,s](q+1) >= D^q max_r alpha[c,r](q)`, and

```text
1 = U[c,0] >= U[c,1] >= U[c,2] >= ... >= theta_c > 0.
```

This is a monotone sequence of **upper bounds**. It is not proved to
converge to `theta_c`. If `D=1`, every quotient is trivial and
`A[c,0](q) = beta^q f_c`; therefore `U[c,q] = 1` at every depth. This method
does not recover the unit-case covering degree.

### Corollary R4 (stronger necessary condition for a strict system)

If a finite fully strict child-closed balanced-pair system exists, the same
argument applied to both tracks gives

```text
theta_c <= U[c,q]/2  for every c and q.                       (2)
```

To see this, fix one balanced source `(u,v)` and inflate by multiples of
`k`. The number of `c`-vertices in each residue class is the same on both
tracks, because their parent Parikh vectors agree. A shared vertex would
be a balanced cut followed by the same letter on both tracks and hence
a coincident factor, contradicting full strict closure. All vertices lie
arbitrarily close to `R_c`: compare a source-letter occurrence with an
occurrence of that letter in `w`; their prefix difference is `M^n z`
for one of finitely many fixed `z`. Count in a regular outer cover as
before, now with twice the mass. This proves (2).

At `q=0`, (2) is the existing one-half necessary condition. At positive
depth it includes the residue concentration. To exclude a strict system
from (2), one still needs a **lower bound** on occupancy, equivalently an
upper bound on area. An upper bound below one half is not such a contradiction.

## 4. The complete depth-two certificate for `1/021/001`

The incidence matrix and its square are

```text
M   = [[0,1,2], [1,1,1], [0,1,0]],
M^2 = [[1,3,1], [1,3,3], [1,1,1]],
det M = 2,
chi_M(x) = x^3 - x^2 - 2x - 2.
```

`M^2` is strictly positive. The only possible rational roots of the monic
cubic are `-2,-1,1,2`, none of which is a root. Its discriminant is `-152`,
so it has one real root `beta`. Since `chi_M(2)<0<chi_M(5/2)`, `beta>2`;
the complex conjugates have squared modulus `2/beta<1`. This establishes
the primitive irreducible non-unit Pisot hypotheses exactly.

An unnormalized positive Perron vector is

```text
F = (beta+2, beta^2, beta),    sum F_c = beta^3.
```

The normalization of `F` cancels in (1). The second-level words are

```text
sigma^2(0) = 021,
sigma^2(1) = 1001021,
sigma^2(2) = 11021.
```

Residues are labelled by `adj(M^2) p(P) mod 4`, where

```text
adj(M^2) = [[0,-2,6], [2,0,-2], [-2,2,0]].
```

This labels exactly **four** classes, isomorphic to `(Z/2Z)^2`; it does
not mean reducing the three prefix coordinates independently modulo four.
The complete nonzero occurrence table is:

| Following letter `c` | Residue key | Counts by source `(0,1,2)` |
| --- | --- | --- |
| 0 | `(0,0,0)` | `(1,1,1)` |
| 0 | `(2,0,2)` | `(0,1,0)` |
| 0 | `(2,2,0)` | `(0,1,0)` |
| 1 | `(0,0,0)` | `(0,1,1)` |
| 1 | `(2,0,2)` | `(1,2,2)` |
| 2 | `(0,2,2)` | `(1,1,1)` |

Every omitted row is zero. The maximizing row for each letter is determined
by componentwise dominance, so no approximate eigenvalue comparison is
needed. Substitution into (1) gives:

| Letter | Exact certified upper bound | Why it is below one half |
| --- | --- | --- |
| 0 | `theta_0 <= (beta+2)/(4 beta)` | `beta > 2` |
| 1 | `theta_1 <= beta^4 / [4(2 beta^2+3 beta+2)]` | `2(2 beta^2+3 beta+2)-beta^4 = beta^3 > 0` |
| 2 | `theta_2 <= 1/4` | `1/4 < 1/2` |

These are inequalities for the true Euclidean occupancies, not values
obtained by rasterizing a projected point cloud. At depth one the selected
rows for letters 1 and 2 give exactly `U[c,1]=1/2`; only the depth-two
certificate makes the strict below-half conclusion for every letter.

## 5. Why this helps the productivity programme

The literal left strong-coincidence witnesses are:

| Pair | Inflation level | Zero-based position | Common prefix Parikh | Next letter |
| --- | --- | --- | --- | --- |
| `{1,2}` | 1 | 0 | `(0,0,0)` | 0 |
| `{0,1}` | 5 | 31 | `(12,13,6)` | 1 |
| `{0,2}` | 6 | 31 | `(12,13,6)` | 1 |

These are exhibited levels, with no claim of optimality. Each witness
persists under further inflation. Consequently every nonempty irreducible
noncoincident balanced pair for this substitution produces a diagonal factor
within six generations: use the witness for its first two letters. Hence
this substitution has **no** fully strict noncoincident child-closed system.
This conclusion is combinatorial and does not depend on occupancy.

The example therefore refutes the proposed converse
`all theta_c <= 1/2 => a strict C4 obstruction exists` within the actual
non-unit Pisot regime. It does not refute the valid implication in (2),
does not settle pure discrete spectrum from strong coincidence, and does
not show that every possible non-unit occupancy bound is useless.

The reusable gain is more specific. A Euclidean calculation can lose
substitution-residue information before it is used in a productivity
argument. The table measures that loss exactly at a chosen finite level.
The compact M-adic lift retains the entire compatible residue sequence and
restores the internal measure scaling used by the graph-directed argument.
That is the setting in which to develop a non-unit cut-pair overlap upper
bound while retaining legal occurrence data.

Word order remains necessary even at depth two: replacing `021` by `012`
preserves `M` but changes the residue table. The zero-residue row for
letter 0 becomes `(1,0,1)`. Incidence/Perron data alone do not determine
the prefix-occurrence certificate.

## 6. Replay and evidence boundaries

Canonical implementation, driver and regression:

- `kernel/psc/c4_nonunit_residue_occupancy.mojo`;
- `kernel/c4_nonunit_residue_occupancy.mojo`;
- `kernel/tests/test_c4_nonunit_residue_occupancy.mojo`.

The independent oracle uses rational Gaussian elimination to obtain
`(M^q)^-1 p(P) mod Z^3`; it does not reproduce the native adjugate
implementation. It checks the full depth-two table, conservation through
six depths, exact refinement through five steps, the polynomial identities,
unit and word-order controls, literal witnesses and refusal cases.

```bash
python tests/test_c4_nonunit_residue_occupancy_oracle.py
cd kernel
pixi run --locked mojo run -I . tests/test_c4_nonunit_residue_occupancy.mojo
pixi run --locked mojo run -I . c4_nonunit_residue_occupancy.mojo
```

The finite kernel's resource bounds are executable limits, not mathematical
hypotheses. An invalid or exhausted input refuses certification. The
analytic results rest on the written arguments above and in the bridge
note; a green finite replay is not a formal verification of those arguments.
The original scratch calculation remains unaudited as a historical object.
The new exact bounds establish its below-half conclusion independently.
