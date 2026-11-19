# Periodic partners after UP′: extraction, zero-fibre anchoring, and collapse

**Status:** Written geometric reductions with an explicitly imported
periodicization theorem, and finite steps checked in Lean. Independent human
review is pending. No strict PIP3 system is excluded; C4 and PSC remain open
and no governed claim changes. This continues
[PR #609](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/609)
from `main@4f8b3581605028b2e842c8b095ccbe164be8bdaa`.

[Pre-code literature decision](c4-periodic-partner-extraction-stop-go-2026-11-18.md)

The proposed next step in the [unique-partner note](c4-unique-partner-exclusion-2026-11-18.md)
has three different parts. **Simultaneous periodicity is available:** a common
translation makes both asymptotic partners and their common partner periodic.
**The identity fibre needs an additional condition:** at a normalized branch,
the differing endpoint letters must never merge. **A contradiction is still
missing:** the two asymptotic partners share tiles, and neither (NM_V) nor
(W4) turns their two strict links into a triangle.

## Work shown

### Assumptions and hypotheses

Use the legal, translation-minimal hull of a primitive irreducible ternary
Pisot substitution `σ`, with inflation homeomorphism `Φ`, expansion `β > 1`,
and the fixed geometric-realization normalization
`h : Ω_σ → 𝕋_A`, `h Φ = A h`. The target is the solenoid in the nonunit
case, not just its zeroth torus coordinate. Its fibres are finite by
[Baker–Barge–Kwapisz, Theorem 4.2](https://www.numdam.org/article/AIF_2006__56_7_2213_0.pdf).
The zero fibre `F₀ = h⁻¹(0)` is permuted by `Φ`. A periodic tiling with a
vertex at the physical origin belongs to `F₀`; this is (R4) of
[round four, §3.1](c4-round4-2026-11-17.md#31-setting), using the integral
strand normalization. Mere existence of a vertex at the origin without
periodicity is not this assertion.

Let `Z` be the strict component of [Theorem W](c4-rank-two-wall-2026-11-16.md#62-statement).
Write `(T,S),(T,U) ∈ Z`, where `S ≠ U` agree on a half-line. Round-four
[Lemma C(c)](c4-round4-2026-11-17.md#33-proofs) supplies such a witness in
the nowhere-locally-injective case left by UP′ under (NM_V), odd determinant,
rank two, and the existence of a strict system.

The roles of the strict-component conditions are separate:

| Input | Use here |
| --- | --- |
| (Z1): compactness, diagonal-flow invariance and invariance under a power of inflation | Common translations preserve both links. Compactness and inflation invariance are needed only for the alternative limit proof below. At rank two, (W1) gives invariance under `Φ` itself. |
| (Z2): relatively dense common vertices and no common labelled tile at any level | The two links are strict. In particular `T` differs from both leaves. The asymptotic leaves cannot be added as a third strict link. Relative density is not needed for the finite-fibre promotion. |
| (Z3): a periodic pair with a common origin vertex exists in `Z` | Supplies an anchored pair somewhere in `Z`; it does not say that this pair has a second asymptotic partner. The quantifiers cannot be combined without a further argument. |
| (Z4): partners lie in the same `h`-fibre | Once the two leaves are periodic, the common partner lies in their finite periodic fibre. When the leaves are in `F₀`, the common partner is there too. |
| (NM_V) | A member of `F₀` asymptotic to a vertex-type member is vertex-type with the appropriate shared letter. It neither puts an arbitrary periodic fibre at zero nor makes a strict partner an asymptote. |
| (W4) | The two partners are densely eventually coincident. This is compatible with their half-line agreement. |

The external geometric input is the statement in
[Barge–Diamond–Swanson (BDS), §2, printed p. 5](https://arxiv.org/pdf/0804.0930):
distinct asymptotic tilings admit a unique common translation making both
inflation-periodic. This is prior art, not a new theorem of this repository.
The source works with the legal minimal hull, and the standing hypotheses
transfer. The earlier paper it cites was not independently re-proved here.
This imported statement is not encoded as an axiom in the Lean modules.

### Derivation / reduction

#### 1. A periodic triple in a periodic fibre

**Lemma P (periodic partner promotion).** Under the preceding inputs, there
are `t ∈ ℝ` and `N > 0` such that

`Φᴺ(T − t) = T − t`, `Φᴺ(S − t) = S − t`, `Φᴺ(U − t) = U − t`,

and both translated pairs belong to `Z`. The two translated leaves are still
distinct and asymptotic. Their common fibre is periodic, but the conclusion
does not identify it with `F₀`.

*Proof.* BDS gives a common translation `t` and a common positive period `q`
for the leaves. Let `p = h(S − t)`. Equivariance gives `A^q p = p`.
Translation invariance and (Z4) put all three translated tilings in the
finite set `h⁻¹(p)`. The injective map `Φ^q` maps this finite set into itself,
hence permutes it. Some further power fixes the common partner as well.
Taking a common multiple of the periods gives `N`. The operation is an
exact translation, so distinctness and the two `Z` memberships are retained
without any limiting argument. ∎

This proof does not use (NM_V), odd determinant, (W4), (Z3), compactness,
or inflation invariance of `Z`. Those inputs belong to the existence or
later analysis of the witness, not to the promotion itself. Nor may one
copy the base period unchanged to its lifts: a permutation of a finite
fibre may have a nontrivial cycle.

#### 2. The branch origin is not automatically the inflation centre

Orient the witness to the right-asymptotic case. Its branch point `x*` is
the first point after which the two tilings agree forever. It is a common
vertex. The tiles immediately to its left have different labels; otherwise
agreement would extend across that tile. Translate the entire triple by
`x*`, so that `S,U` now agree on `[0,∞)` and branch at `0`. Let `b ≠ c` be
the labels of their tiles ending at `0`, and let `g_R` be the last-letter
map of `σ`.

This translation fixes the branch origin. BDS's translation fixes the
inflation centre of a periodic pair. In general these are different
origins; translating an already periodic pair to a branch point need not
preserve periodicity about the unchanged inflation origin.

**Lemma E (exact endpoint criterion).** For this branch-normalized pair,
the following are equivalent:

1. `g_R^n(b) ≠ g_R^n(c)` for every `n ≥ 0`.
2. `S` and `U` are fixed by a common positive power of `Φ`.
3. `S,U ∈ F₀`.

When these conditions hold, the simultaneously translated common partner
`T` is in `F₀` and is periodic too. For a left-asymptotic pair, interchange
left and right and use `g_L` on the different letters starting at `0`.

*Proof of 1 ⇒ 2.* Apply BDS to obtain `t,q` such that `S − t,U − t` are
fixed by `Φ^q`. Their branch point is `y = −t`, and the letters immediately
to its left are still `b,c`. Substitution sends the common right half-line
to the half-line starting at `β^q y`. The two tiles ending there have
different labels `g_R^q(b),g_R^q(c)`, so `β^q y` is exactly the branch point
of the inflated pair. The pair is fixed, hence `y = β^q y`. Since `β > 1`
and `q > 0`, `y = 0` and `t = 0`. This is the argument of round-four Lemma A
with the endpoint hypothesis made explicit.

*Proof of 2 ⇒ 1.* For a common period `q`, the endpoint letters at the
origin return: `g_R^q(b) = b` and `g_R^q(c) = c`. An equality at any
iterate would persist to a sufficiently large multiple of `q` and imply
`b = c`, a contradiction.

*Proof of 2 ⇔ 3.* Periodicity and a vertex at the origin give membership in
`F₀` by (R4). Conversely the finite set `F₀` is permuted by the injective
map `Φ`, so its members have a common positive period. Finally (Z4) puts
the common partner in this same fibre. ∎

For three letters the infinite hypothesis in item 1 is an exact finite
test:

`g_R²(b) ≠ g_R²(c)`.

Lean proves this equivalence for **every** map `Fin 3 → Fin 3`, not just
maps arising from a sampled substitution. After two iterations every
letter is on a cycle of period dividing six. Injectivity of the relevant
endpoint map is sufficient for the test. If the side of the Lemma C(c)
witness is not prescribed, injectivity of both endpoint maps covers either
orientation. This does not assert that (NM_V) implies endpoint injectivity
or that an arbitrary (NM_V) witness passes the test.

There is also a proof of the **existence** of a zero-fibre triple under the
same persistence condition that does not use BDS. Inflate twice, then in
steps of six. The leaves' central substituted left and right tiles grow
on both sides to two legal periodic seam tilings, and their left labels
remain different. Compactness supplies a subsequential limit of the common
partner. Closedness and inflation invariance of `Z` retain both links;
(Z4) then puts the limit partner in `F₀`. With only (Z1), choose iterations
compatible with its exponent `P`; (W1) already gives `P = 1`. This
alternative may produce a different triple. Lemma E proves the stronger
claim about the original branch-normalized triple.

#### 3. What fails when the endpoint letters merge

**Lemma M (collapse of unshifted inflation).** If
`g_R^m(b) = g_R^m(c) = d` for some `m`, then

`d(Φⁿ S, Φⁿ U) → 0` as `n → ∞`.

In particular every convergent subsequence of unshifted inflated triples
has identical second and third coordinates.

*Proof.* The pair `Φ^m S,Φ^m U` still agrees on `[0,∞)` and has a common
tile of type `d` ending at `0`. Thus it agrees on `[-ℓ_d,∞)`, where
`ℓ_d > 0` is that prototile's length. After `k` further inflations the
agreement interval contains `[-β^k ℓ_d,∞)`. Every fixed compact
neighbourhood is eventually contained in that interval. This proves
convergence of the distance to zero and forces equal leaves in any common
subsequential limit. ∎

The mirror proof uses `(-∞,β^k ℓ_d]`. No rank assumption or (NM_V) enters.
This is a concrete obstruction to “inflate and take a limit while keeping
two distinct partners.” It does not obstruct BDS's common translation,
which still gives a periodic triple in some periodic fibre.

#### 4. The extracted configuration does not close a triangle

From `(T,S),(T,U) ∈ Z` one knows noncoincidence of `T` with each leaf.
The leaves `S,U` themselves share a half-line, so they share labelled tiles
already at level zero. Adding `(S,U)` to `Z` would violate (Z2).
At rank two, (W4) expressly permits and requires dense eventual coincidence
between the leaves. This is the same distinction used in the first part
of [Barge's Lemma 13](https://arxiv.org/pdf/1301.7094); its final uniqueness
conclusion assumes an additional triviality condition on the stack relation.

Nor can the letter count from UP′ be copied into this case. Its distinct
partner letters came from covering Lemma C(b), and its matching of partners
along an asymptotic edge came from covering Lemma L. The new witness has
two different partners with a repeated letter on their shared side.
Those covering premises are precisely what is unavailable.

Even when the leaves are vertex-type in `F₀`, the common partner might be
interior-type. (NM_V) does not make it vertex-type: a strict partner cannot
be asymptotic to either leaf, because it shares no tile with that leaf.
A new global argument is needed to obtain a different pairwise
noncoincident triple or to propagate an appropriate letter relation.

### Evidence and replay

The two new modules are
[`PeriodicPartner.lean`](../proof/PscVerif/PscVerif/PeriodicPartner.lean) and
[`PeriodicPartnerControls.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerControls.lean).
They contain no tiling-space axioms. Their scope is finite fibres,
iteration, finite relations, literal words, and integer identities:

- `periodic_lift_of_finite_fibre` proves a positive lift period divisible
  by the specified positive base period; `common_period_three` combines
  three periods.
- `endpoint_persistent_iff` proves the two-step criterion for every ternary
  endpoint map; `endpoint_period_six` verifies the cycle bound;
  `endpoint_merge_persists` keeps an equality at all subsequent depths.
- The control module checks the finite data in the next section, including
  a connected six-seam model where distinct asymptotic partners do not
  force a triangle or the regular-graph parity count.

Replay with the repository's pinned Lean/Lake release and dependencies:

```sh
cd proof/PscVerif
lake build PscVerif.PeriodicPartner PscVerif.PeriodicPartnerControls
```

The modules are imported by the complete proof-bank root and covered by
its generated inventory and axiom audit. The scoped clean-source replay is
`./tools/check_c4_periodic_partner.sh`, also run by the
[revision-specific workflow](../.github/workflows/c4-periodic-partner.yml).
It compiles both modules from fresh sources against fresh pinned dependency
checkouts and audits all owned compiled declarations, including generated
helpers, against the source theorem inventory. It reuses no local compiled
objects. The separate full-bank replay is `./tools/check_lean.sh`;
passing the scoped check does not claim a full-bank replay. Local and hosted
acceptance evidence is recorded in the pull request. None of these checks formalizes BDS, the tiling
topology, legal infinite limits, geometric realization, (NM_V), or (W4).

### Negative controls

#### The documented (NM_V) failure `1/012/21`

Let `σ(0)=1`, `σ(1)=012`, `σ(2)=21` and

`M = [[0,1,0],[1,1,1],[0,1,1]]`, `x = (1,0,-1)`,
`w = 122`, `v = 210`, `W = 121`.

Lean checks the following exact identities and finite legality witnesses:

`σ(w) = 0 w W`, `σ(v) = v W`, `M x + e₀ = x`,

`x + p(w) = p(v) = (1,1,1)`,

`σ²(1) = 101221`, `σ²(2) = 21012`.

Here `p` is the Parikh column. The patch `w` based at `x` retains itself
in its substitution, with nonempty extension on both sides. Its nested
inflations give a legal `Φ`-fixed tiling `U`. Equivalently retain the
central `1` in `σ(1)=0·1·2`: putting `a=-x`, the return equation is
`(M-I)a=e₀`. The positive eigenlength row satisfies

`(β−1)ℓ(a)=ℓ₀ > 0`,

`(β−1)(ℓ₁−ℓ(a))=ℓ₂ > 0`.

Thus the retained `1`-tile based at `x` contains the origin strictly.
This is the existing interior-address construction, and it needs no
floating estimate of the Perron root.

The legal periodic vertex tiling `T_(1,2)` has the ray starting with `v`,
because `v` is a prefix of `σ²(2)` and `σ(v)=vW`. Both it and `U` have the
same infinite right tail after the strand vertex `z=(1,1,1)`:

`W σ(W) σ²(W) ...`.

Their tiles ending at `z` differ (`0` in the vertex ray, `2` in the other
patch), so their branch is there, at physical position `ℓ(z)>0`, rather
than at the inflation centre. The vertex tiling is in `F₀` by (R4), and
asymptoticity gives `h(U)=h(T_(1,2))=0` by round-four (E1). Hence an
interior member of `F₀` is
asymptotic to a vertex-type member: (NM_V) fails as documented in round
four. The finite identities are machine-checked; this infinite-tiling
interpretation is the written argument above.

The endpoint maps are `g_L=(1,0,2)` and `g_R=(1,2,1)`. In particular
`g_R(0)=g_R(2)`. Translating this pair to its branch origin therefore puts
it in the merging case of Lemma M, and the unshifted inflation limit
collapses. The example tests the proposed construction without being a
strict rank-two counterexample and without contradicting Lemma E.

#### Nonzero periodic fibre in the literature

BDS Example 3 uses the two-letter substitution
`1→1122111`, `2→1211111221`, with matrix
`A=[[5,7],[2,3]]`. Its periodic asymptotic pairs lie over nonzero classes
`(1/3,2/3)` and `(2/3,1/3)` in the paper's integral normalization. The
integer check `A(1,-1)=(1,-1)+(-3,0)` makes the first class fixed and
nonzero modulo three. This refutes “periodic asymptotic implies zero
fibre” under primitive irreducible unit Pisot hypotheses alone. It has
two letters and is not an example of a strict PIP3 joining at rank two.

#### A connected finite model without the proposed contradiction

Take the seam set `E = {0,1,2} × {0,1}`, whose letter graph is the
connected `K₃,₂`. Define a symmetric partner relation by

`P((a,b),(c,d)) ↔ b ≠ d and exactly one of a,c equals 0`.

Every seam has a partner, partner endpoints differ on both sides, and the
partner graph has no triangle. The seam `(0,0)` has the two partners
`(1,1)` and `(2,1)`, sharing their right letter. Degrees are two on the two
seams with left letter zero and one on the other four seams. The connected
letter graph has cycle rank `6−3−2+1=2`; even the numerical cohomological
lower bound `3+2=5` does not refute this model.

Declare two seams equivalent when their right letters agree and either
both left letters are zero or neither is zero. This is an equivalence
relation; all partners of one seam are equivalent, and a seam is not
equivalent to its own partner. Declare all six objects vertex-type and
coordinate equality to be the corresponding one-sided asymptotic relation.
The finite type-preservation condition is then satisfied.

Lean checks these assertions over the complete finite sets. They show that
these **finite consequences** of symmetry, (Z2), vertex type, and partner
equivalence do not force a triangle, a uniform degree, or a fixed-point-free
letter involution. The model does not implement tiling flow, inflation,
minimality, dense eventual coincidence, or a geometric realization map.
It is therefore not a model of the full geometric (Z1)–(Z4), (NM_V), and
(W4) assumptions, and not a counterexample to C4 or PSC.

#### The rank-three triangle `012/120/201`

The cyclic relabelling `ρ:0→1→2→0` commutes with this substitution; its
three cyclic partners form a triangle. The literal control checks the
commutation and full bigram data, retaining the correction in UP′:
its swap-closed partner graph is a rank-at-least-three control, not a
rank-two example. Its incidence matrix is singular, so it cannot satisfy
the nonsingular irreducible PIP3 setting used in Lemmas P and E.

Finally the two-element transposition over a fixed singleton base checks
that “fixed base ⇒ fixed lift” is false. Lemma P must allow a multiple of
the base period.

### Non-claims / remaining gaps

The periodicity part of the old “next statement to try” is resolved,
conditional on the cited published import. The following geometric
obligations are still exact and separate:

1. **Selection or treatment of a branching witness.** Under the surviving
   strict rank-two hypotheses and (NM_V), show that some witness can be
   selected whose differing endpoint letters pass the two-step test, or
   analyze the periodic branch fibres that do not meet this branch-origin
   criterion. Lemma C(c) does not select endpoint labels, and (Z3)'s
   anchored pair need not be the same witness.
2. **A contradiction after successful zero-fibre extraction.** Control the
   common partner's vertex or interior type and the repeated-letter
   multiplicities without using the covering-only matching lemma. Prove a
   genuinely new global obstruction or produce a different triple whose
   three pairs are noncoincident. The extracted asymptotic leaves cannot
   themselves provide the third strict edge.
3. **Geometric formalization.** The legal hull, asymptotic periodicization,
   origin/fibre correspondence, branch-location argument and collapse
   argument remain written mathematics. Lean checks the finite deductions
   and controls, not these geometric hypotheses or their realization.

No assertion here makes (NM_V) universal, removes the even-determinant
covering residue of UP′, or constructs a rank-two PIP3 strict system.
