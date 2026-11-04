# Literature gate: which Arnoux–Ito subtile family is the positive-prefix `R_c`? — 2026-11-04

**Status:** stop/go note (AGENTS.md "Targeted literature stop/go check") for
promoting Lemma P of [the cut-pair note §4](c4-cut-pair-productivity-2026-11-04.md#4-source-audited-subtile-comparison-convention-corrected-2026-11-04).
It moves no governed claim status.

## Proposed claim

Let `σ` be primitive and unimodular with irreducible Pisot incidence. Let
`R_c = closure{π p(P) : P c prefix of a fixed point}` (positive-prefix,
Euclidean). If `{c,c'}` has a left strong-coincidence witness, then
`λ(R_c ∩ R_c') = 0`.

## Prior art and terminology

1. **Arnoux–Ito 2001** (Bull. Belg. Math. Soc. 8, pp. 181–207). Read directly
   in the published text.
   - Def. 6 defines the primed domain `D_n(i)'` as `π(E1*(σ)^n(0, e_i*))` and
     the unprimed `D_n(i)` as `π(E1*(σ)^n(−e_i, e_i*))`.
   - Lemma 1 gives
     `E1*(σ)(x, e_i*) = Σ_{j,k: W_k^{(j)} = i} (E0(σ)^{-1}(x − f(P_k^{(j)})), e_j*)`.
   - Def. 11 defines a *positive strong coincidence of order 1 for i, j* by
     `W_k^{(i)} = W_k^{(j)}` and `f(P_k^{(i)}) = f(P_k^{(j)})`. That is a
     left (prefix) witness.
   - Cor. 2: the volume vector is a Perron eigenvector.
   - Proof of Thm 2, first sentence: "if σ has a positive strong coincidence
     of order 1 for i, j, X(i)'∩X(j)' is of measure 0". The all-pair
     hypothesis is used only afterwards, to transfer disjointness to the
     unprimed `X(i)`.
2. **Siegel–Thuswaldner**, *Topological properties of Rauzy fractals*,
   Mém. SMF 118 (2009), Thm 2.6. Pairwise strong coincidence gives
   measure-disjoint subtiles in the unit case. This is reported by the
   exploration audit and not re-read here.
3. **Minervino–Thuswaldner 2014.** The non-unit analogue lives on the adelic
   representation space.
4. **Akiyama–Barge–Berthé–Lee–Siegel 2015** survey. Unconditional
   disjointness is listed as open.

## What transfers

Iterating Lemma 1 from `(0, e_i*)` gives faces with base points `−M^{-n} f(Q)`,
one for each occurrence `σ^n(l) = Q i S`. Renormalised by `M^n`, the primed
limit is `X(i)' = −R_i`. Starting from `(−e_i, e_i*)` gives
`X(i) = −(R_i + πe_i)`, the suffix family.

So the positive-prefix `R_c` is the **primed** family up to the map `x ↦ −x`,
which preserves measure. The Arnoux–Ito pairwise statement therefore applies to
`R_c` verbatim.

The revision of 2026-11-04 (#480) labelled `R_c` "unprimed" and withdrew the
pairwise statement. That withdrawal was a labelling error.

## What does not transfer

- **Unimodularity.** It is essential: for `|det M| ≥ 2` the measure
  inequality forces nothing.
- **Non-unit Euclidean statements.** None follows.
- **Suffix witnesses.** A right (suffix) witness nulls the translated pair
  `(R_c + πe_c) ∩ (R_c' + πe_c')`, not `R_c ∩ R_c'`.

## Negative controls / boundaries

- No unit Pisot substitution failing pairwise strong coincidence is known
  (Arnoux–Ito §6). The implication
  `SC(A(C)) ⇒ disjoint(A(C)) ⇒ no strict C` is therefore no stronger than
  Theorem A(4).
- Nakaishi arXiv:1610.03146 is withdrawn. arXiv:2401.07771 was audited in
  `nakaishi-2024-first-entry-audit-2026-10-13.md` and not imported. Neither
  may be cited for unconditional disjointness.

## Decision

**Proceed, narrowed to the unimodular case.** Lemma P carries a
self-contained proof in the cut-pair note §4:
- the set equation of `R_y` for a power `τ`;
- the inequality `β^m v ≤ M^m v` and equality after pairing with `ℓ > 0`;
- distinct source letters at the same translate.

Novelty: none. This is Arnoux–Ito's statement read through the convention
dictionary. The repository value lies in correcting the wrong withdrawal.
