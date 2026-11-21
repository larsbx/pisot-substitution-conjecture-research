# Word rigidity of the nonunit C4 stack quotient

**Status.** Written proof that a primitive irreducible nonunit Pisot
substitution on three letters at coincidence rank two has no strict
system. This covers the even-determinant residue. The finite algebra
has scoped Lean checks. Independent review is pending.

## Literature decision

| Source | Transfer |
| --- | --- |
| [Barge, *Factors of Pisot tiling spaces*, Theorem 12, §4 and Proposition 19](https://www.numdam.org/item/10.24033/bsmf.2691.pdf) | The stack projection from a proper return presentation is a subdivision morphism. Stack pullback on rational first cohomology is injective. These results have no odd-norm condition. |
| [Barge–Diamond, *Cohomology in one-dimensional substitution tiling spaces*, Theorem 4 and proof](https://arxiv.org/pdf/math/0702669) | The equivariant exact sequence accounts for all nonzero cohomology eigenvalues using the original incidence and the eventual range. A common power fixes the eventual-range graph. |
| [Fenn–Sjerve, *Basic commutators and minimal Massey products*, §4](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/D2D3FEEB1C2D7AE1A7EB6B9BD792CAF7/S0008414X00022501a.pdf/basic-commutators-and-minimal-massey-products.pdf) | The ordered expansion `a ↦ 1 + X_a` is classical. For positive words the top coefficient already detects the word. |
| [Horn–Johnson, *Matrix Analysis*, Theorem 2.4.4.1](https://studylib.net/doc/25868436/matrix-analysis--roger-a.-horn--charles-r.-johnson-) | Disjoint spectra make the Sylvester operator invertible. The proof below also gives its homogeneous argument. |

**Decision.** Lift the length labels through the actual stack
subdivision. Nonunit algebraic norm separates higher tensor degrees
from the edge spectra. Two periodic raw lifts of one stack tiling
then give the obstruction. Thue–Morse tests the need for independent
raw lengths, and a unit determinant tests spectral separation.

## Work shown

### Assumptions and hypotheses

Let `σ` be a primitive irreducible Pisot substitution on three letters
with nonunit incidence and coincidence rank two. Suppose it has a
strict system. Even nonzero determinant implies nonunit.

By (W1) of [Theorem W](c4-rank-two-wall-2026-11-16.md#62-statement),
the strict joining is swap-invariant and its bigon substitution is
primitive. [Theorem NI(2)](c4-rank-two-wall-2026-11-16.md#5-non-injectivity-of-the-top-track-theorem-ni)
then gives two distinct periodic partners `T,T′` of one tiling.
By (W4), the partners have the same stack image, and the positions
of their eventual tile coincidences form a dense set. Write
`q : Ω → X` for the stack quotient.

Take a common positive inflation power fixing `T,T′` and the original
eventual-range graph and inducing a proper return substitution.
Use `M` and `β` for the powered original incidence and dilation.
The original unpowered incidence has irreducible characteristic
polynomial and three conjugate eigenvalues. The eigenvalues of `M` are their corresponding powers,
with `β > 1` the simple Perron eigenvalue. Let `V = ℚ³` and
`ℓ : V → ℝ` be the original length map. The kernel of `ℓ` is invariant
under the original unpowered irreducible incidence, so `ℓ` is injective.
We have `ℓ(Mv) = β ℓ(v)`.

### Derivation / reduction

#### Graph presentations at original letter cuts

The raw letter graph `A` is a wedge with one oriented edge per original
letter. Its edge substitution is the literal powered word substitution
and its edge matrix is `M`. The proper return graph `R` is a wedge
with one edge per return word. Its graph map parses each inflated
return word into return words. Choose a marker at a legal periodic
letter cut. A sufficiently high common power starts all return
images with the same return word inside the inflated right marker
letter, and ends all images with the same return word inside the
inflated left marker letter. Such complete first and last return
words exist by uniform recurrence. The reblocking preserves the
translation and powered inflation actions.

Insert all original letter cuts into the edges of `R`. The
flattening map `ρ : R → A` sends each subdivided edge to its raw
letter. It commutes with inflation because the return substitution
parses the literal inflated word between its inherited marker cuts.

Take the proper stack graph `S` for this return presentation.
Barge's subdivision morphism `s : R → S` follows stack tiles across
each return word and preserves length. Insert into `S` the images
of all subdivided return vertices, together with the existing stack
vertices. This finite set is forward invariant. A raw letter cut
inflates to a raw letter cut and `s` commutes with inflation. Stack
vertices are inherited under stack inflation. The two maps are
now length-preserving edge-path maps and commute with inflation on
literal paths. The refinements subdivide the existing graph edges
and preserve their inverse limits. In the raw letter graph only the
edge substitution is used.

#### Chain spectra and length coordinates

For each refined graph let `B` denote the inflation operator on its
rational oriented edge chains. For a graph presenting a hull, the
nonzero spectrum on its cycle space is the spectrum of the induced
map on rational first Čech cohomology, with the same multiplicities.
Indeed, `H₁ = ker ∂`, the graph cohomology is its dual, and the direct
limit deletes the nilpotent part. The remaining quotient of the edge
chains is `im ∂`, an invariant subspace of the vertex chains. A map
of a finite set of vertices has only zero and roots of unity in its
spectrum.

On `R` the Barge–Diamond exact sequence has the incidence part
`Mᵗ` and fixed eventual-range terms. In particular its cohomology
has only eigenvalues of `M` and roots of unity, and `β` has
multiplicity one. Proposition 19 injects `H¹(X; ℚ)` equivariantly
into this space. Thus on `A,R,S` every edge eigenvalue is zero, a
root of unity or an eigenvalue of `M`.
The multiplicity of `β` on the stack edge chains is at most one
and is exactly one because the positive length row is a left
`β`-eigenvector.

Let `β₀` be the unpowered Perron root and put `K = ℚ(β₀)`.
For any nonzero original length `c`, the three independent rational
vectors `c, β₀c, β₀²c` lie in `ℓ(V)`, so `ℓ(V) = cK`.
The powered `β` belongs to `K`. For the refined stack
graph, the equation for the left `β`-eigenrow is a linear system over
`K` with a one-dimensional real solution space. Take a nonzero row
over `K`. Its real scale is fixed by the length of `s(e)` for one
subdivided raw-letter edge `e` of `R`. That length is a positive
original letter length, and `s(e)` is an integral edge path.
Consequently the scale belongs to `ℓ(V)` and all refined stack edge
lengths belong to `ℓ(V)`.

On every graph, label an oriented edge by the unique vector in `V`
giving its length. The labels are preserved under each edge-path map
after summing on paths. Inflation transforms their sum by `M`.
Both statements follow by applying the injective length map `ℓ`.

#### Higher-degree lifts of the length labels

Use the truncated tensor algebra
`T≤r(V) = ℚ ⊕ V ⊕ ··· ⊕ V^⊗r` with concatenation of tensor factors
and products above degree `r` set to zero. Seek a label `g_r(e)`
with constant term one and degree-one term the edge vector. Require
multiplication in occurrence order on paths and the inflation equation

```text
g_r(f(e)) = T≤r(M) g_r(e).
```

At degree one this holds by the length identity. Suppose the labels
are constructed below degree `j`. Write `D_j = M^⊗j`. The unknown
degree-`j` labels define a linear map
`C : ℚ^(edges) → V^⊗j`. A change in the top component of a factor in a
path product is multiplied only by the constant terms of the other
factors. The degree-`j` component of the inflation equation therefore
has the form

```text
D_j C − C B = E_j,
```

where `E_j` is the already determined degree-`j` path product with all
unknown top components set to zero.

The spectra of `B` and `D_j` are disjoint for every `j ≥ 2`.
To see this, work in a splitting field `L/ℚ` containing the original
cubic roots and the roots of unity in the finitely many edge spectra.
For each of the three powered roots the absolute field norm is the
same number `D = |det M|^([L:ℚ]/3) > 1`. Galois transitivity on the
original roots gives this identity even when a power is used. A tensor eigenvalue is a product
of `j` powered roots and has absolute norm `D^j`. The eigenvalues
allowed for `B` have absolute norm `0`, `1` or `D`.
This separates the spectra.

For an explicit Sylvester argument, if `D_j C = C B` then
`χ_B(D_j) C = C χ_B(B) = 0`. Cayley–Hamilton and spectral separation
make `χ_B(D_j)` invertible, so `C = 0`. The Sylvester operator
acts on a finite-dimensional rational vector space, so injectivity
gives a unique solution for any `E_j`. This proves existence and
uniqueness at every finite truncation.

Pullback along a graph map evaluates the target labels on the image
paths. It gives an equivariant assignment with the same degree-one
labels on the source. Uniqueness gives `ρ* g_A = g_R = s* g_S`
at every truncation.

#### The periodic lifts agree

Take two common raw vertices `a < b` of `T,T′`. The two return
paths along `[a,b]` may start and finish inside return words, at
vertices of the subdivision of `R`. Their images in `S` are
the same literal path. They follow the common stack tiling
`q(T) = q(T′)` on exactly that interval, and the subdivision
of `S` includes the two endpoints. Each stack path product
equals the corresponding raw word product via `R`. Thus the
two raw words `u,v` have `g_A(u) = g_A(v)` at every finite
truncation.

For an original letter `a`, the label on `A` has the form
`1 + X_a +` higher terms, where `X_a` is the corresponding basis
vector of `V`. The usual ordered product `E(w) = ∏(1 + X_a)` separates
positive words. A word's top monomial is the word itself with
coefficient one. If `u ≠ v`, take the least nonzero degree `j` in
`E(u) − E(v)`. Replacing each `X_a` by `g_A(a) − 1` in degree
at most `j` acts as the identity on this first nonzero component.
It preserves its coefficient because the linear terms are exactly
the distinct basis vectors. This gives different products at
truncation `j`, a contradiction.

Consequently the tilings agree between any two common raw vertices.

By (W4) choose an eventual common tile containing a point on the
negative side and one containing a point on the positive side,
each at its own inflation level. Inflate both coincidences to a
common higher multiple of the period of `T,T′`. A common tile
inflates to a common patch. Since the tilings are fixed under
this power, the two patches give common raw vertices of
`T,T′` on opposite sides of zero. Further common powers send
these vertices arbitrarily far left and right while keeping the
tilings fixed. Their agreement between common vertices now
gives `T = T′`, contradicting the choice of two distinct partners.

### Evidence and replay

| Lean endpoint | Checked step |
| --- | --- |
| `tensor_norm_separates` | Products of at least two equal-norm roots have norm outside the edge spectrum's allowed values |
| `pathProduct_add_correction` | Changing the top-degree part adds the corrections in occurrence order |
| `sylvester_exists_unique` | An annihilator of the edge operator acting injectively on the target gives a unique correction for each residual |
| `pullback_equivariant`, `same_stack_interval_products_eq` | Commuting path projections preserve the assignments and a shared stack interval has equal raw products |
| `fixedTilings_eq_of_common_intervals` | Agreement on common-vertex intervals and one common cut on each side imply equality of inflation-fixed tilings |

The module is [PeriodicPartnerStackWordRigidity](../proof/PscVerif/PscVerif/PeriodicPartnerStackWordRigidity.lean).

```sh
cd proof/PscVerif
lake build PscVerif.PeriodicPartnerStackWordRigidity
lake env lean PeriodicPartnerAudit.lean
cd ../..
./tools/check_c4_periodic_partner.sh
python3 tools/make_proof_bank.py --check
```

### Negative controls

- For Thue–Morse both raw letter lengths are equal. The one-dimensional
  length labels do not distinguish the letters, and the balanced words
  `01` and `10` can have the same product. Its stack covering and odd
  winding are compatible with this calculation.
- For a unit cubic the product of its three eigenvalues is the
  determinant, hence is `1` or `−1`. With determinant `1` the tensor
  spectrum already meets the neutral eigenvalue in degree three.
  With determinant `−1`, the square of that product yields `1` in
  degree six. The nonunit hypothesis is needed for the separation
  argument.

### Non-claims / remaining gaps

The geometric graph construction, its rational cohomology spectrum,
the identification of the norms with Galois conjugates, and the
assembly of the graded lift are written mathematics. Independent review
is pending. Higher coincidence ranks and extraction of a finite strict
carrier from arbitrary nonproductivity are separate obligations.

**Review, 2026-11-20.** A [step-by-step check](c4-stack-rigidity-review-2026-11-20.md)
against Barge's text found no gap. It records a rank-free form of the core lemma and the
resulting higher-rank obligation in the nonunit case.
