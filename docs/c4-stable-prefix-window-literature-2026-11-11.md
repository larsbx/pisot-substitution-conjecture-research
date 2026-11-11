# Literature gate: actual stable-prefix windows

Date: 2026-11-11. This gate precedes new proof code and continues the
literal-prefix construction of [PR #542](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/542),
source `aa80845e9ccde9f4a0c90c00d1f6d6ade40559b5`. It also reuses the
existing [finite-cylinder verifier](c4-finite-cylinder-overlap-verifier-2026-11-04.md)
and its [source gate](c4-finite-cylinder-overlap-literature-gate-2026-11-04.md).
The side-notes ledger was inspected before selecting this target.

## Stop/go decision

**Proceed with the actual-prefix compact-window theorem and its explicit
contraction premises.** Derive a uniform bound for every prefix of the
same infinite word used to define `PrefixClosure.prefixTiles`. This
removes the supplied all-prefix enclosure premise once the local digit
bound, commuting contraction, and word fixedness have been proved.

Do not implement a second finite-cylinder diagnostic. The canonical
verifier already checks exact stable-coordinate block contraction and all
block digits for `1/021/001` and `1/012/001`. Its calibration is block
length `12`, contraction bound `7/8`, digit bound `5`, and radius `40`.
Those are existing executable certificates; this continuation concerns
the missing deductive bridge to actual infinite prefixes. Exact native
certificate acceptance and a Lean proof about a supplied bound remain
distinct unless a checked decoder or formal fixture proves their link.
Section 3 of the older verifier note obtains its radius by maximizing
over already compact tiles. That written argument bounds such tiles but
cannot independently establish the compactness premise left in PR #542;
the actual-prefix induction below avoids that circular use.

The bounded-prefix argument is standard. The contribution here is its
mechanically checked specialization to the repository's literal address
identities, its original matrix-adic carrier, and its precise period and
scope boundaries. No novelty is claimed for stable contraction,
Dumont--Thomas expansions, compact Rauzy sets, or geometric-series bounds.

## Primary sources inspected

| Primary source and location | Relevant result | Transfer boundary |
| --- | --- | --- |
| Pierre Arnoux, Masahiro Mizutani and Tarek Sellami, *Random product of substitutions with the same incidence matrix*, [arXiv:1301.7316](https://arxiv.org/abs/1301.7316), [primary PDF](https://arxiv.org/pdf/1301.7316), Lemma 3.1 and Proposition 3.2, pp. 8--9 of the preprint. | An actual prefix decomposes into substituted local prefixes. Projection commutes with the common incidence matrix; an adapted contracting norm and finitely many digits bound the projected prefix by a geometric series. The associated prefix closures satisfy the graph-directed set equation. | The section assumes a positive primitive unimodular Pisot matrix. The finite-digit norm estimate itself uses commutation and contraction, not determinant one. Reprove that estimate with its actual hypotheses; do not import the paper's later unimodular tiling conclusions into the nonunit carrier. |
| Marcy Barge and Jaroslaw Kwapisz, *Geometric theory of unimodular Pisot substitutions*, American Journal of Mathematics 128 (2006), 1219--1282, [author-hosted primary PDF](https://math.montana.edu/jarek/documents/papers/AJM2006.pdf), Section 5 and Lemma 5.1, p. 1233. | In an adapted stable seminorm, substitution is a uniformly bounded perturbation of its linear incidence action. The radius transforms as `R -> mu R + alpha`; a radius above `alpha/(1-mu)` is invariant. | The strand-space and canonical-torus framework has additional hypotheses. Only the stated radius estimate is the template here. An adapted norm or a certified contracting block must be supplied; an arbitrary coordinate norm need not contract in one step. |
| Milton Minervino and Jorg M. Thuswaldner, *The geometry of non-unit Pisot substitutions*, Annales de l'Institut Fourier 64 (2014), 1373--1417, [journal record](https://aif.centre-mersenne.org/item/AIF_2014__64_4_1373_0/), [primary preprint](https://arxiv.org/pdf/1402.2002), Sections 3, 4.4 and 6. | The nonunit representation retains finite completions. Section 4.4 relates prefix-automaton expansions, their compact projective limit, and contracting internal coordinates; Section 6 separates the cut-and-project realization and its point-set equations. | The repository's `H_M` is the explicitly constructed matrix-adic carrier. Its existing compactness and residue proofs may be used directly. No unproved identification with the paper's full adelic representation, Haar normalization, regular-window density, or tiling theorem is imported. |

The first two sources independently exhibit the same finite-digit
contraction mechanism. The third checks that using it does not erase the
nonunit arithmetic factor. None licenses inferring C4 or pure discrete
spectrum from compactness.

## Proposed theorem and derivation

Fix a substitution `tau`, an infinite word `w` fixed by `tau` in the
existing full-prefix sense, an additive coordinate map `pi`, and an
additive action `B` satisfying

\[
B(\pi z)=\pi(M_\tau z),\qquad
\|Bx\|\le q\|x\|,\qquad 0\le q<1.
\]

Let `D >= 0` bound the norm of `pi(parikhZ P)` for **every literal proper
prefix** `P` in an image `tau(a)`. This is a finite set determined by the
whole image words, including repeated selected-letter positions. One may
derive `D` from that finite set or supply a separately authenticated bound.
Let `R >= 0` satisfy `q R + D <= R`; `D/(1-q)` is the standard choice.

For the actual projected prefix `x_n = pi(parikhZ(wordPrefix w n))`, the
existing complete literal address theorem gives a parent index `i`, an
actual local prefix `P`, and

\[
x_n=B x_i+\pi(\operatorname{parikhZ}P).
\]

Nonerasure supplies both complete addressing and `i <= n`. Strong
induction on `n` now gives the bound without assuming strict length
growth or an already compact tile:

1. If `i < n`, the induction hypothesis gives
   `norm(x_n) <= q R + D <= R`.
2. If `i = n`, the same identity gives
   `(1-q) norm(x_n) <= D <= (1-q) R`. Since `1-q > 0`, it gives the bound
   directly. The equality case must not be silently discarded.

Thus every actual prefix lies in `closedBall 0 R`. In a proper normed
space that ball is compact. The existing
`PrefixClosure.prefixTiles_compact_of_window` then proves compactness of
the defined closures in `E x H_M`; its history-piece theorem transfers
this result to every finite literal inverse history.

This proof is an alternative organization of the standard finite-prefix
expansion argument. It uses exact ordinal identities already established
in `PrefixAddress`, not a sampled prefix cloud or a hypothesized
attractor's boundedness. A productive-seed wrapper can instantiate its
fixed-word hypotheses using the existing `seedWord` construction.

## Period and realization boundaries

If contraction is certified only at block length `m`, use
`tau = sigma^m`, action `B^m`, and **all prefixes of the literal block
images**. Word fixedness must hold at that same exponent. A word fixed
only by `sigma^k` is fixed by suitable multiples of `k`; the exponent
compatibility must be proved, not inferred from incidence equality.
The original `H_M` and its corresponding level-`m` detector remain the
arithmetic carrier; no replacement by a different inverse limit is
implicit.

The existing finite-cylinder chart is
`W x = (x0-a*x1, x2-b*x1)`, with `a=(beta+2)/beta^2` and `b=1/beta`.
Its checked polynomial identities give `W M = B W` for `B = W M J`,
`J=[e0 e2]`. Reuse this construction and its exact arithmetic if binding
the two existing fixtures. A theorem for an arbitrary supplied
commuting contracting action is not yet a general constructor of the
intended stable representation from primitive irreducible Pisot input.

Contraction alone does not supply a closed embedding: the zero map is a
contracting counterexample to injectivity. Compactness of prefix closures
does not require that embedding premise, but the existing tile-equation
and inverse-cover results still retain it. A finite-dimensional injective
linear realization can discharge it through its own proof.

## Negative controls and evidence obligations

- Preserve the existing all-erasing fixed-prefix control. Fixed-prefix
  equality without cofinal addressing does not authenticate a tile
  equation. The proposed proof explicitly requires nonerasure or the
  separate addressing and parent-index facts it supplies.
- Preserve the expanding-real control `sigma=00/1/2`, `w=000...`,
  `pi(z)=z0`, `B(x)=2x`: actual prefix points are unbounded. Its contraction
  premise fails.
- Retain the `i=n` parent case; a proof that assumes every parent has
  smaller ordinal adds an unjustified expansion premise.
- Reject a block-digit bound based on a truncated inventory or only the
  original one-step images. Certified contraction of `B^m` needs the
  complete depth-`m` digits.
- Reject a radius with `q R + D > R`, or a contraction bound with
  `q >= 1`. Equality `q R + D = R` is valid; strict separation is needed
  for `q < 1`, not for the radius inequality.
- Keep existing wrong-period, missing-commutation, and continuous-but-not-
  closed controls from the prefix-closure note.
- Preserve the mandatory `00/11/22` inverse-closed forward-leak control
  with physical calibration `full=4`, `retained=2`, `positive_exits=2`.
  Compact prefix windows do not turn this physical diagnostic into
  compact-overlap measure.

Acceptance requires compilation under the pinned Lean toolchain and the
complete axiom audit, inclusion in the generated proof bank, explicit
checks of the weakened-premise controls, and truthful exact-revision
replay receipts. No reported execution follows merely from this gate.

## Remaining obligations

The target advances the actual geometric enclosure used by PR #542.
It does not prove an arbitrary input is Pisot, construct all stable
spectral data automatically, deserialize native certificates into Lean,
construct a complete finite global ancestor domain, prove forward
completeness, identify product Haar scaling, establish an additive
overlap-measure recurrence, or provide strict-cut-root positivity.
Issue #461 and the general C4, G1, Concentration and PSC obligations
remain open; no governed claim is promoted by this gate.
