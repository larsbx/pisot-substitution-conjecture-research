# Literal prefix points and their closure equation: literature stop/go gate

**Decision (2026-11-11): proceed with exact literal prefix addressing,
the raw prefix-point equation, and its passage to closures under an
explicit continuous closed action.** This gate is recorded before the
new Lean, canonical Mojo, and independent-oracle implementation. The
construction will define the sets from an actual supplied right-infinite
word, rather than assume a tile equation for an unspecified family. It
will not yet prove compactness in an authenticated Pisot stable space,
finite forward completeness, a Haar-measure recurrence, or C4.

The starting implementation is PR #541 head
`1e3aa8e046c8f82df5e2792f4118a345033a5e07`, merged as
`2848e5f67b605669a550f362a1de4bf1c1529f7c`. The actual merge tree
`257877c09ab7819d21fd53622a337ed6f4a3c936` equals that of the accepted
core implementation. At the start of this gate, seven broader PR
workflows were still pending, with no reported failure; this statement
does not treat those pending workflows as completed acceptance.

## 1. Question, policy, and inspected repository interfaces

The review read `AGENTS.md`, the relevant
[side-notes ledger](side-notes-ledger.md) entries,
[the matrix-adic gate](c4-madic-residue-literature-2026-11-11.md),
[its resulting boundary](c4-madic-residue-2026-11-11.md), and the existing
fixed-word, literal-address, occurrence-cover, and residue modules.
The targeted question is whether the supplied `TileEquation` premise
can now be proved for closures of actual prefix points, while retaining
literal occurrence multiplicities and an explicit word-period scale.

The useful existing interfaces are:

- `FixedPointLimit.limit_fixed_eq` supplies the full fixed-prefix identity
  for its constructed limit, under its stated prolongability and growth
  hypotheses. `Binomial.subst_power` identifies a substitution power with
  iteration. These results do not themselves define topological tiles.
- `OccurrenceAddress.locateSubst`, its index/prefix/selected identities,
  and `locate_subst_position` preserve parent ordinal and local position.
  `OccurrenceTransport.Mark` retains the whole before/letter/after split;
  `Mark.inflate` and `parikhZ` substitution identities already support the
  required prefix calculation.
- `OccurrenceInverse.iterateImages` and `incidenceZ_iterateImages`
  retain the chosen power and its incidence action.
- `MadicResidue` supplies the actual coherent quotient carrier, continuous
  action, injectivity under integral-action injectivity, and compactness
  for the finite free integer-module setting. `OccurrenceResidue`
  supplies conditional cover and profile consumers, including explicit
  empty-tile controls. Neither module yet defines these literal prefix
  closures or proves their tile equation.
- `PerronExistence` provides Perron data, but the inspected interfaces do
  not provide the required stable projection and uniform prefix bound.
  `OverlapContraction` contains conditional uniqueness/period arguments;
  it does not instantiate the compact-set system for these prefix sets.

The contribution at this stage is the repository-specific formal bridge
and its exact address certificates. The underlying substitution and
closure identities are established mathematics.

## 2. Primary sources inspected

| Primary source | Material inspected | Transfer and boundary |
| --- | --- | --- |
| [Minervino--Thuswaldner, *The geometry of non-unit Pisot substitutions*](https://arxiv.org/pdf/1402.2002), Section 2.1, Remark 7.8, Proposition 8.1, and Theorem 8.3(i), equation (28) | Nonerasing substitutions and periodic words; prefix-automaton indexing; closures of projected prefix vertices; the prefix-indexed set equation. | The paper supplies the closest geometric construction. Its authenticated nonunit representation uses completion fields and additional geometric hypotheses. Its compactness, measure-disjointness, interior, tiling, and Haar conclusions are not transferred merely by matching an equation. |
| Mathlib at the repository pin `4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09`: [maps and closed embeddings](https://github.com/leanprover-community/mathlib4/blob/4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09/Mathlib/Topology/Maps/Basic.lean), [closure](https://github.com/leanprover-community/mathlib4/blob/4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09/Mathlib/Topology/Closure.lean), [Hausdorff spaces](https://github.com/leanprover-community/mathlib4/blob/4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09/Mathlib/Topology/Separation/Hausdorff.lean), and [product maps](https://github.com/leanprover-community/mathlib4/blob/4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09/Mathlib/Topology/Constructions/SumProd.lean) | Actual locally installed source for `IsClosedMap.closure_image_eq_of_continuous`, `closure_iUnion_of_finite`, `Continuous.isClosedEmbedding`, and `Topology.IsClosedEmbedding.prodMap`. | These exact pinned APIs support the closure passage and product instantiation. Continuity alone gives only one inclusion for image and closure. A finite incoming-mark family is essential to the finite-union step. |
| [Stacks Project, Lemma 5.17.7, tag 08YD](https://stacks.math.columbia.edu/tag/08YD), and [Section 5.17, Lemma 5.17.8, tag 005M](https://stacks.math.columbia.edu/tag/005M) | A continuous map from a quasi-compact space into a Hausdorff space is closed; a continuous bijection between such spaces is a homeomorphism. | Applied to the map onto its image, these justify the compact-carrier closed-embedding argument. They do not make the stable coordinate compact, nor make a product with an unbounded prefix set compact. |

These three primary-source families cover the closest construction, the
exact software theorem interfaces, and the topology needed to avoid the
unjustified continuity-only argument. The derivations below are the
proposed specialization to this repository, not a claim that a cited
paper already provides these exact Lean statements.

## 3. Literal word hypotheses and complete occurrence addressing

Let the alphabet be `Fin 3`, let `tau` map letters to finite words, and
let `w : Nat -> Fin 3`. Write

\[
P_w(n)=w[0,n),\qquad b(n)=|\tau(P_w(n))|.
\]

The full fixed-prefix hypothesis is

\[
P_w(b(n))=\tau(P_w(n))\quad\text{for every }n.       \tag{F}
\]

For a nonerasing substitution, `b(n+1) > b(n)` and `b(n) >= n`, so every
output position lies in a unique substituted parent block. A useful
stronger core theorem can instead assume just the explicit productivity
condition

\[
\forall m\;\exists n,\quad m<b(n).                  \tag{P}
\]

Together, (F) and (P) also handle erasing substitutions whose output
prefixes remain unbounded: zero-length parent blocks simply contain no
local marks. Nonerasing remains the requested convenient sufficient
condition and should be exposed as a corollary. Neither (F) alone nor a
bounded list of checks for (F) establishes (P) or infinite fixed-word
coverage.

The exact address constructor is

\[
(i,d)\longmapsto b(i)+d.\mathrm{index},\qquad
d:\operatorname{Mark}(\tau(w(i))).                 \tag{2}
\]

The target is a bijection between all output positions and the dependent
family of actual parent/local marks. Its proof may work inside a large
enough finite substituted prefix, using the existing complete literal
lookup and its uniqueness. For the address of `m`, the required identity
is

\[
P_w(m)=\tau(P_w(i))\,d.\mathrm{before},\qquad
w(m)=d.\mathrm{letter}.                            \tag{3}
\]

The record retains parent ordinal, local index, source letter, and the
full before/selected/after split. Equal letters, repeated image blocks,
equal Parikh vectors, and equal residues do not identify these records.
There is no claim that the eventual projected points are distinct: even
the zero star map can collapse every point. Address multiplicity and
set support are separate outputs.

## 4. Exact raw equation, then its closure equation

Let `G` be an additive commutative group, let
`star : Z^3 ->+ G`, and let `A : G ->+ G`. Assume the exact commutation

\[
A(\operatorname{star}(z))
  =\operatorname{star}(M_\tau z)\quad\text{for all }z,       \tag{C}
\]

where incidence acts on column vectors. Define actual prefix-point sets

\[
\operatorname{Raw}_c
  =\{\operatorname{star}(\operatorname{parikhZ}P_w(n)):
       w(n)=c\}.
\]

Let `D_c` be the finite family of all pairs `(a,d)` with
`d : Mark(tau(a))` and `d.letter = c`. Under (F), (P), and (C), the
strongest immediate raw conclusion is

\[
\operatorname{Raw}_c
 =\bigcup_{(a,d)\in D_c}
    \bigl(A(\operatorname{Raw}_a)
            +\operatorname{star}(\operatorname{parikhZ}d.\mathrm{before})
     \bigr).                                             \tag{R}
\]

Here the plus sign means translation of the image set. Both inclusions
use actual addressed occurrences, not an arbitrary digit list.
Topology, injectivity, primitivity, irreducibility, the Pisot property,
compactness, and measure are unnecessary for (R). The set equality does
not assert a disjoint union or a multiplicity-weighted measure identity.

Now give `G` a topological additive-group structure and define

\[
K_c=\overline{\operatorname{Raw}_c}.
\]

Assume `Continuous A` and `IsClosedMap A`. Translation is a
homeomorphism, so each affine branch is continuous and closed. The exact
pinned API gives

\[
\overline{A(S)}=A(\overline S).
\]

Using finiteness of `D_c`, take closures in (R) to obtain

\[
K_c=\bigcup_{(a,d)\in D_c}
      \bigl(A(K_a)
          +\operatorname{star}(\operatorname{parikhZ}d.\mathrm{before})
      \bigr).                                           \tag{T}
\]

This is the intended `OccurrencePiece.TileEquation` for the *defined*
prefix closures. A closed embedding is a sufficient stronger hypothesis
on `A`, and also supplies injectivity for downstream piece identities.
Alternatively, compactness of every `K_a`, continuity of `A`, and a
Hausdorff target would suffice for the relevant image/closure equalities.
The proposed route uses closedness to prove (T) before the stable-prefix
compactness theorem has been established. No continuity hypothesis on
the discrete star domain is needed for the raw calculation.

## 5. Actual matrix-adic product and the chosen period

For the original integral incidence action `M`, retain the actual

\[
H_M=\varprojlim_q\mathbb Z^3/M^q\mathbb Z^3
\]

already implemented in PR #541. Its action `T` is continuous and is
injective when `M` is injective. In this finite free integer setting the
carrier is compact Hausdorff. Consequently `T` is a closed embedding by
the inspected compact-to-Hausdorff theorem.

Let `E` be a topological additive group with an additive closed embedding
`B : E -> E`, and an additive map `pi : Z^3 -> E` satisfying
`B(pi z) = pi(M z)`. With the actual matrix-adic star `iota`, put

\[
\operatorname{star}(z)=(\pi z,\iota z),\qquad
A(e,h)=(B e,T h).
\]

The product-map theorem makes `A` a closed embedding; its commutation is
the coordinatewise identity. This establishes the hypotheses for the
closure equation relative to the supplied `E`, `B`, `pi`, and `w`.
It does not identify that supplied data with the intended Pisot stable
realization. In particular, compactness of `H_M` says nothing by itself
about boundedness in `E`.

If the word is fixed only under `tau = sigma^k`, retain that scale:
use the literal marks of `tau`, incidence `M^k`, and action `A^k`.
Closed embeddings remain closed embeddings under composition. The same
`H_M` and its level-`k` residue map are available; there is no need to
assume or prove an unimplemented identification with `H_(M^k)` merely to
state this theorem. Do not infer the original one-step equation, or
independence of the chosen fixed word, from a power equation alone.
Those conclusions require their own argument, such as an appropriately
instantiated contraction/uniqueness theorem.

## 6. Required negative controls and bounded certificate boundary

| Unjustified stronger statement | Reproducible control and required distinction |
| --- | --- |
| The full prefix identity (F) alone supplies all output positions. | Set every image to the empty word and take `w = 000...`. Then (F) holds vacuously, but there are no local marks. With the trivial star map, `Raw_0` is nonempty while the proposed incoming union is empty. Keep (P), or nonerasing, explicit. |
| An arbitrary right-infinite word may be used as though it were fixed. | For `tau = 1/0/2` and `w = 000...`, with the trivial star map, `Raw_0 = {0}` but its only incoming parent is letter `1`, whose raw set is empty. The word is fixed by `tau^2`, so this also prevents silently discarding the period scale. This is an abstract control, not a primitive irreducible Pisot instance. |
| Commutation (C) may be omitted. | For `tau = 00/1/2`, `w = 000...`, `G = Z`, `star(z) = z_0`, and the zero action `A`, the raw set for letter `0` is the nonnegative integers, whereas the incoming right-hand side is only `{0,1}`. |
| A continuous map commutes with closure of an image. | The continuous additive endomorphism `A(x,y) = (x,0)` of `R^2` sends the closed hyperbola `S = {(x,y): xy = 1}` to `(R \ {0}) x {0}`, which is not closed. Thus `closure(A(S))` strictly contains `A(closure(S))`. The closed-map premise cannot be deleted. |
| Closure commutes with an arbitrary incoming union. | The union of the closed singletons `{1/n}` for positive integers `n` acquires `0` in its closure. The actual branch index is finite; an infinite-union extension needs a separate hypothesis. |
| A closed product action and an exact prefix-closure equation imply compact tiles. | Take `sigma = 00/1/2`, `M = diag(2,1,1)`, `w = 000...`, `E = R`, `B(x) = 2x`, and `pi(z) = z_0`, with the actual compact `H_M`. Then `K_0 = {(n,iota(n e_0)): n >= 0}` is closed and satisfies the even/odd prefix equation, but is unbounded in its first coordinate and not compact. The other two tiles are empty. This deliberately expanding `E` is not the intended stable realization. |
| A prefix equation makes every letter tile nonempty, or identifies positions after projection. | In the preceding `000...` word, letters `1` and `2` never occur. A zero star map collapses all prefix points even while literal parent/local records remain different. Nonempty contributing parents are still needed for full digit-profile equality, and multiplicities must remain in the records. |
| Inverse closure or an incoming equation proves forward completeness. | Retain `00/11/22` and the selected states `(0,1,0)` and its track swap. Each source has four forward positional pairs: one retained positive pair, one positive exit, and two outside pairs with zero physical calibration. Across both sources the existing receipt is `full = 4`, `retained = 2`, `positive_exits = 2`. Those are positive-calibration totals, not counts of all positional pairs. This remains a physical diagnostic, not a compact-Haar measure identity. |

For finite computational work, a source word `u` may certify the exact
bijection between positions of `tau(u)` and its parent/local full marks.
The certificate must bind the entire source word and entire expanded
target word, before/selected/after slices, global index, and prefix
identity. A truncated target cannot be accepted as the whole expanded
window. Checks of finitely many windows cannot establish (F) or (P) for
all natural numbers. Canonical Mojo and an independent integer oracle
should validate these finite claims with independently reconstructed
literal records; neither residue-set equality nor total-count equality
alone is sufficient. No new native receipt or artifact count is claimed
by this pre-code gate.

## 7. Minimal remaining authentic geometry

The proposed work removes the *supplied tile-equation* premise for sets
defined from a word and realization that meet the explicit hypotheses.
It does not yet authenticate the intended compact PSC tiles. The next
minimal geometric input for compactness is a compact stable-coordinate
window `C` containing every actual prefix projection:

\[
\forall n,\quad
\pi(\operatorname{parikhZ}P_w(n))\in C,
\qquad C\subset E\text{ compact}.                       \tag{B}
\]

In a proper finite-dimensional stable space, a proved uniform boundedness
statement can supply (B). Together with the already compact `H_M`, it
places the raw sets in a compact product; with the needed Hausdorff
topology their closures are compact. The stable projection, its action,
and the word admissibility must first be identified with the intended
Pisot data. No current finite quotient computation supplies this bound.

If every letter occurs in the supplied word, nonempty prefix closures
follow immediately; that occurrence premise should be proved from the
chosen word/substitution hypotheses or left explicit. It must not be
inferred just from (F). An abstract graph-directed attractor can be
compared with these literal prefix closures only after an applicable
uniqueness argument has been established.

Even after compactness, complete representation by a selected finite
ancestor domain, forward-exit exclusions, nonunit product-Haar scaling,
and a link from strict cut roots to positive overlap measure remain
separate obligations. Literal occurrence multiplicities must remain
available throughout. Physical interval lengths cannot substitute for
compact-overlap measure.

## 8. Stop/go decision

**GO:** formalize the literal address bijection and exact prefix identity
under (F) and (P), expose the nonerasing corollary, define `Raw` and its
closures, prove (R), prove (T) under continuous closed `A`, and instantiate
the closed-action hypothesis on the actual `E x H_M` product under the
stated assumptions. Carry the chosen substitution power explicitly.
Finite executable artifacts may certify only their complete literal
windows and their stated integer claims.

**STOP at the documented boundary:** do not call these arbitrary supplied
realizations authentic compact Pisot tiles, infer compactness without
(B), infer a one-step equation from a power equation, replace occurrence
counts by support cardinality, or erase positive forward exits. No
governed C4, global G1, Concentration, or general Pisot Substitution
Conjecture claim is promoted by this gate.
