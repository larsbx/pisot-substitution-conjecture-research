# Finite lower count for the original balanced cuts

This increment proves a finite count on the original integer Parikh vectors
and binds those same vectors to the named physical strip and compact-open
capture theorem. It is implemented in `StrictCutCount` and `NamedCutCount`.
The implementation subject is commit
`31f8046291f2428e839d95e8890c8342858ec210`, tree
`e38c3f65efb79fa72860d8ef222e96695847a551`.

## Mathematical result

For balanced words `u,v`, write `bs = red u v`. Each
`j : Fin bs.length` selects the original prefix vector before the j-th
factor occurrence:

\[
z_j=\operatorname{Parikh}_{\mathbb Z}
\left(\operatorname{flatten}\bigl((\operatorname{take}_j bs).\operatorname{map}(\mathrm{fst})\bigr)\right),
\qquad Z=\{z_j:j\in\operatorname{Fin}(bs.\mathrm{length})\}.
\]

Every reduced factor has a nonempty top word. Consequently, ordinary
prefix lengths strictly increase between occurrences. Equal Parikh
vectors would imply equal ordinary lengths, so `factorStart` is injective
and `Z.card = bs.length`. Repeated equal factor labels still contribute
different occurrences and different starts.

Complete reduction reconstructs both original words. At each counted
start, `exists_balanced_marks_of_mem` constructs genuine top and bottom
marks, retaining their entire prefix, following letter, suffix and splitting
equation. Their integer prefix vectors equal the selected `z`.

For any real letter weights `ℓ` and real upper bound `L`, the generic
finite theorem states

\[
\left(\forall B\in\operatorname{red}(u,v),\;
  \operatorname{physicalLength}_{\ell}(B.1)\le L\right)
\Longrightarrow
\operatorname{physicalLength}_{\ell}(u)\le L\,|Z|.
\]

No sign premise on `ℓ` or `L` is needed for that exact finite sum bound.
The separate strip theorem assumes strictly positive letter weights and
gives `0 ≤ offset ℓ z < physicalLength ℓ u` for every `z ∈ Z`.
These are proper starts: zero is included when a factor exists, and the
terminal endpoint is excluded. An empty factor list contributes no starts.

## Named carrier and one eventual threshold

For either named fixture, fix a finite carrier `C`, a supplied actual
`StrictSystem`, and a uniform carrier bound
`∀ B ∈ C, physicalLength physicalRow B.1 ≤ L`. For `T ∈ C`, set

\[
Z_n(T)=\operatorname{startVectors}\left(
  \operatorname{red}(\sigma^{12n}(T.1),\sigma^{12n}(T.2))\right),
\qquad X_n(T)=\beta^{12n}\operatorname{physicalLength}_{\mathrm{physicalRow}}(T.1).
\]

`integerStarts_count_and_strip` proves, for every `n`,

\[
X_n(T)\le L\,|Z_n(T)|,
\qquad
\forall z\in Z_n(T),\quad 0\le\operatorname{offset}(z)<X_n(T).
\]

Strict carrier closure supplies the factor bound after any number of
substitutions. A private whole-word induction supplies the exact physical
scaling, and the named positive row supplies the strip hypothesis.

For any fixed open `U` containing `carrierOverlap fixture C`,
`eventually_integerStarts_mem` gives

\[
\exists N\;\forall n\ge N\;\forall T\in C\;\forall z\in Z_n(T),
\quad \operatorname{ambientStar}(z)\in U.
\]

It applies the actual marks to the compact-neighborhood theorem of #558,
so the represented `CutPair C` labels and the original matrix-adic carrier
are retained. One threshold works over the fixed finite carrier. Cardinality
is taken only in integer Parikh space; no injectivity of `ambientStar` or
of anchored reference-witness ordinals is used.

The carrier bound is an explicit hypothesis. Finiteness provides such a
bound mathematically, but this increment does not export a separate positive
maximum constructor, a divergence theorem, or a normalized density limit.

## Verification

The unchanged isolated `./tools/check_lean.sh` completed successfully with exit zero at 2026-11-12T21:08:49.179037+00:00 (elapsed 3155.19 seconds) at the exact
implementation revision above. Its source hashes, HEAD and tree remained
unchanged throughout the run. The [evidence packet](../evidence/c4-finite-cut-count-2026-11-12/README.md)
preserves the genuine start snapshot, terminal process receipt, complete
raw log, source inventory, compiled inspection and supporting reviews.

| Check | Recorded result |
| --- | --- |
| Complete pinned Lean build | 9025 jobs completed |
| Full compiled audit | 6646 declarations, including 4865 theorem constants |
| Exact new source inventory | Nine public theorem declarations, three private proof helpers and three definitions |
| New-module compiled inventory | 18 constants, including 15 theorem constants and compiler-generated auxiliaries |
| Axiom dependencies | Only `propext`, `Classical.choice`, and `Quot.sound` |
| Proof bank | 126 governed claims, all 2,705 named proofs reached, 411 source openings |
| Governance | Terminology, claims, coverage, promotion, numerics and consistency passed |
| Generated ledger | All 32 generated surfaces current |

The source count includes twelve named proofs: nine public declarations
and three private helpers. Compiled totals also include generated
declarations and are reported separately. The earlier PR description's
focused compilation results remain historical assertions; the complete
run recorded here supplies the new local acceptance. Hosted outcomes are
recorded separately at their observed revisions, and independent human
review remains pending.

## Review chronology and controls

The earlier compact-neighborhood evidence supplied the proposed count
plan and interface review. It did not record the fresh pre-code literature
gate requested for this increment. The present [contract and literature audit](../evidence/c4-finite-cut-count-2026-11-12/review/postimplementation-literature-audit.md)
examines the already implemented source and is explicitly postimplementation.
Its six primary sources support proceeding with unchanged verification;
this does not retroactively change the implementation chronology.

The new compiled controls cover repeated factor labels and the empty list.
The repeated-label example concerns the generic injectivity theorem; its
sample factors are not asserted to form a balanced reduction. Complete
marks and the positive-weight strip theorem retain the proper-endpoint
boundary. The reviews also check empty words, erasing substitutions,
nonpositive abstract weights and the need for a sign premise when enlarging
the counted set; these additional observations are not new compiled
counterexample declarations.

## Replay and remaining obligations

From the repository root with the pinned toolchain installed:

```sh
python tools/make_proof_bank.py --check
./tools/setup_lean.sh
./tools/check_lean.sh
```

The unchanged verifier copies sources and configuration to a fresh
workspace, checks the dependency pins, uses the fixed upstream source-hash
cache, builds the entire project and audits all local compiled declarations.
It does not credit retained local project artifacts. Later report and
evidence commits change no tested proof source or verification tool.

The analytic upper count and positive-overlap argument remain unproved by
this increment. A [separate future design review](../evidence/c4-finite-cut-count-2026-11-12/future/cell-packing-literature-review.md)
proposes disjoint anisotropic fundamental cells in the full physical,
stable and matrix-adic space. Equal fundamental-domain mass could provide
a fixed positive finite cell mass, and finite packing into a measurable
rectangle could then combine with this count and the existing open capture.
That route still requires actual cell, translation, measure, contraction
and growth proofs. Its planned order is a fixed open set, then a fixed cell
depth, then a sufficiently large inflation; no such cell theorem is compiled
here. Exact covolume and full lattice asymptotics remain separate stronger
targets.

### Pre-code decision for the following increment

**Proceed with the narrowed fundamental-cell packing target.** In the actual
physical/stable/matrix-adic product, prove that the cells
`Phi(M^q Q) x ker(eval_q)` are measurable fundamental domains for the same
diagonal integer action, with common mass `0 < c < infinity`, then derive
`c * card Z <= (X + L_q) * mu(O)` for a finite set of original cuts
with `0 <= offset(z) < X`, once the cell translates are enclosed in
`[0, X + L_q] x O` for the fixed open target `O` of finite measure.
The physical cell bound, shrinking internal projection and open capture
must establish that enclosure.
The [primary-source gate](../evidence/c4-finite-cut-count-2026-11-12/future/cell-packing-literature-review.md)
identifies fundamental-domain measure equality and finite packing as
standard tools; the proposed contribution is their actual-model binding.

The hypotheses to retain are the invertible real chart, the nonsingular
actual incidence map and its compatible real extension, the original
matrix image lattice at the same depth as the residue kernel, measurable
cells, exact coverage and disjointness, translation-invariant product Haar
measure, and a fixed open target chosen before the cell depth. The full
space has a compact matrix-adic factor, so real-vector-space covolume APIs
do not apply to it directly. Use the coordinatewise half-open cube:
product-order `Set.Ico 0 1` admits upper-face duplicates. Neither the
nonunit representation results in the cited papers nor this design review
supplies an identification or a missing Lean lemma for the repository's
actual carrier. The [interface review](../evidence/c4-finite-cut-count-2026-11-12/future/cell-packing-route-review.md)
lists the remaining formal obligations and the required order of choices.

No governed claim status changes. No positive Haar measure, strict-system
existence, archived-domain coverage, C4, or general PSC conclusion is
promoted by this increment.
