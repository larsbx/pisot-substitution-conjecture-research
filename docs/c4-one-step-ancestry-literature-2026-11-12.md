# Ordinary inverse ancestry: source gate before implementation

Decision recorded on 2026-11-12 (UTC): **proceed with a narrowed, fully marked
path-composition and root-padding theorem for the two original substitutions.**
The inspected baseline is main
`88ffdac059e14c33b0c181ed829b6e7de3287251`, the merge of #552. This review
precedes new theorem-facing code. It follows `AGENTS.md`, the append-only
side-notes ledger, and the archived graph-refinement and payload-import source
gates. It is a research-design decision, not independent human review or an
acceptance receipt for the proposed theorem.

## Exact proposed claim

Write `s = substitution fixture`, for `fixture : Fin 2`, and retain the
original six ordered roots `ArchivedRoot`: the three packets
`(0,1,0)`, `(0,2,0)`, `(1,2,0)` and their track swaps. The proposed inclusion is

```lean
Ancestry s ArchivedRoot u →
  Ancestry (iterateImages s 2) ArchivedRoot u
```

`Ancestry` is the already defined reflexive-transitive closure of actual
`InverseOccurrence` records, in the direction current child to inverse
ancestor. It is not a path in a newly sampled finite graph. Establish the
inclusion by composing consecutive original occurrences and, for odd paths,
prepending an actual original occurrence from another archived root.

This inclusion alone extends the accepted nullity theorem to every ordinary
inverse ancestor, and gives membership in the existing ordered finite table
whenever its named geometric overlap is nonempty. To advertise the stronger
**ordinary rooted-domain equivalence**, also prove the converse inclusion:
split each actual squared occurrence into two original occurrences, retaining
its complete outer and local marks. The existing generic `locateSubst` lookup
is available to prove this split for arbitrary substitutions; the complete
named digit dictionary provides an additional source-specific check. Together
the two directions give equality of the rooted ancestry predicates under the
explicit incoming root-predecessor hypothesis. Do not infer this converse
from the forward inclusion.

## Six primary-source checks and their scope

1. **Minervino--Thuswaldner, _The geometry of non-unit Pisot
   substitutions_**, [primary preprint](https://arxiv.org/pdf/1402.2002),
   sections 2.1--2.2, PDF pages 3--4, and Theorem 8.3(i), PDF page 19.
   The prefix automaton labels an occurrence by a literal prefix/letter/suffix
   decomposition, and the iterated prefix-suffix development composes those
   decompositions. Replacing a periodic substitution by a power is standard.
   These statements motivate literal two-level address composition; they do
   not identify reachability from a fixed root set at odd and even path
   lengths. Their adelic tile equation is for the paper's specific tiles.
   It does not supply a one-step equation for the repository's period-two
   prefix closures. No such geometric identification is proposed here.
2. **Thuswaldner, _Unimodular Pisot substitutions and their associated
   tiles_**, [primary publication](https://www.numdam.org/item/JTNB_2006__18_2_487_0.pdf),
   Definition 3.6 and Remark 3.7, printed pages 508--510; Lemma 3.8,
   printed page 510. The paired occurrence graph retains two orientation
   alternatives and rooted walks. This supports keeping ordered literal
   tracks and exact endpoint conventions when composing paths. Its setting
   is unimodular, and its subsequent boundary representation assumes super
   coincidence. Neither hypothesis is transferred to these determinant-two
   fixtures. Its special identification of certain diagonal parallel edges
   is not a license to collapse the archived positional slots.
3. **Pinned formal occurrence construction**, baseline
   [`OccurrenceTransport.lean`](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/88ffdac059e14c33b0c181ed829b6e7de3287251/proof/PscVerif/PscVerif/OccurrenceTransport.lean)
   and
   [`OccurrenceInverse.lean`](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/88ffdac059e14c33b0c181ed829b6e7de3287251/proof/PscVerif/PscVerif/OccurrenceInverse.lean),
   with the generic `locateSubst` decoder in
   [`OccurrenceAddress.lean`](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/88ffdac059e14c33b0c181ed829b6e7de3287251/proof/PscVerif/PscVerif/OccurrenceAddress.lean),
   inspected from the local exact-revision checkout. `Mark.inflate`,
   `Mark.inflate_index`, `residual_inflate`, `InverseOccurrence.ofMarks`,
   `InverseOccurrence.swap`, `incidenceZ_iterateImages` and `Ancestry`
   establish the actual source/address conventions. In particular, the
   inverse equation has **bottom prefix minus top prefix**. A generic
   combinatorial composition theorem can use these existing identities.
   `locateSubst_index`, `locateSubst_prefix` and `locateSubst_selected`
   recover the actual source ordinal and local position of every selected
   substituted letter; erasing images elsewhere are explicitly allowed.
   The full mark is fixed by its word and position, so this supports a
   generic inverse to literal mark inflation, and hence a generic
   square-step iff two original steps. These arguments require no new
   geometric, measure, primitivity or Pisot premise.
4. **Pinned exhaustive named digit source**,
   [`NamedArchivedDigits.lean`](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/88ffdac059e14c33b0c181ed829b6e7de3287251/proof/PscVerif/PscVerif/NamedArchivedDigits.lean).
   `digitEquiv` exhausts all 15 actual squared occurrences;
   `square_word`, `digit_inflate`, `digit_before_inflate`,
   `digit_after_inflate` and `flat_eq_nested_index` retain the parent,
   both positional levels, both complete prefixes and both suffixes.
   These are sufficient source data for splitting named squared
   occurrences. Equal letters or equal endpoints do not identify marks.
5. **Pinned named word/geometry boundary**,
   [`NamedPrefixCompact.lean`](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/88ffdac059e14c33b0c181ed829b6e7de3287251/proof/PscVerif/PscVerif/NamedPrefixCompact.lean).
   `sigma0`, `sigma1`, `substitution`, `word_fixed_two`,
   `word_not_fixed_one` and `tileEquation_two` fix the literal sources and
   their established period. The current named words are not fixed by one
   substitution application. That fact blocks relabelling the existing
   fixed-prefix argument at exponent one; it does not itself disprove every
   possible one-step tile equation. The proposed route needs no such equation.
6. **Strongest accepted domain and measure consumer**,
   [`ArchivedPayloadConsumer.lean`](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/88ffdac059e14c33b0c181ed829b6e7de3287251/proof/PscVerif/PscVerif/ArchivedPayloadConsumer.lean),
   with its source-bound `NamedArchivedGraph` dependency.
   `Packet.rooted_nonempty_domain_iff` and `Packet.ancestors_null` use the
   original squared ancestry, the same named overlap sets, and a valid
   original archived payload. The measure conclusion retains an explicit
   probability additive Haar measure on the original matrix-adic factor.
   Path conversion can feed these consumers without changing any archived
   graph, potential, box, geometric exclusion or measure normalization.

These sources support an elementary specialization of standard composition
and reachability arguments. The intended contribution is their complete
formal source binding for these two named fixtures, not a new general tiling
criterion or a new spectral argument.

## Exact sufficient hypotheses and literal derivation

For a generic directed relation `R` and its two-step composition `R²`, the
sufficient root hypothesis is

```text
for every r with Root r, there is q with Root q and R q r.
```

This is an incoming root predecessor in the **current-to-ancestor** direction.
An even path pairs directly. Prepend `q → r` to an odd path before pairing.
Length-zero paths remain rooted length-zero paths. No finiteness, positivity,
nonemptiness of overlaps, injectivity of the incidence matrix, or one-step
tile equation is needed for this path argument. The hypothesis is sufficient;
no necessity claim is intended.

For `e : InverseOccurrence s p v` and
`f : InverseOccurrence s v u`, compose the outer marks of `f` with the local
marks of `e`. If `M = incidenceZ s`, and `a_e,b_e,a_f,b_f` denote their top
and bottom prefix Parikh vectors, the equations give

```text
M δv  = δp + b_e − a_e
M δu  = δv + b_f − a_f
M² δu = δp + M(b_f − a_f) + (b_e − a_e).
```

The composed top prefix is `subst s f.topMark.before ++ e.topMark.before`;
the composed bottom prefix has the same formula with bottom marks. This
matches `residual_inflate` literally. Preserve the corresponding suffixes
and the index formula, using the actual intermediate letters to align the
dependent marks. Track swap swaps both levels and negates the integral
offset. Never reverse only the endpoints or only the residual sign.

For the converse split, `locateSubst` supplies outer and local marks of any
selected substituted word. Its prefix and index equations, together with
the full mark's fixed suffix, identify inflation with the original mark.
For these named fixtures the exhaustive squared mark dictionary also records
the same outer and local data. Define the intermediate packet from the outer marks and the
ancestor's integral offset by the forward formula
`δv = M δu + a_f − b_f`. This is integral by construction. The squared
inverse equation then yields the local inverse equation. Both original
occurrences are therefore needed; checking just the squared incidence
equation with guessed intermediate letters is not sufficient.

The following literal witnesses discharge the named root-predecessor
condition. With the generic square-step equivalence this supplies the full
rooted ancestry equivalence, in addition to the inclusion. All root offsets
are zero, and all listed positions are zero-based.
Here `q → r` means `InverseOccurrence s q r`.

| Ancestor root `r` | Fixture | Prepending root `q` | Positions in `s r.top`, `s r.bottom` | Both literal prefixes |
| --- | --- | --- | --- | --- |
| `(0,1,0)` | either | `(1,0,0)` | `(0,0)` | empty |
| `(0,2,0)` | either | `(1,0,0)` | `(0,0)` | empty |
| `(1,2,0)` | `1/021/001` | `(2,0,0)` | `(1,1)` | `[0]` |
| `(1,2,0)` | `1/012/001` | `(1,0,0)` | `(1,1)` | `[0]` |

Every prepending packet is itself an archived root orientation. Equal
prefixes make the required residual exactly zero. The other three ordered
roots follow by swapping both tracks, using `archivedRoots_swap` and the
actual occurrence swap. These are source-specific witnesses, not an inference
from the common incidence matrix.

## Counterexamples and required controls

- **No predecessor, parity transfer fails.** Let the sole edge be `r → u`,
  with root set `{r}`. Then `u` has ordinary ancestry and no rooted path
  in the squared relation. Duplicating this example with the two tracks
  interchanged also refutes any attempt to use swap closure alone.
- **Outgoing is not incoming.** With roots `{r,t}` and edges
  `r → t`, `t → t`, `r → u`, every root has an outgoing edge to a root,
  but `u` still has no rooted even-length path. Padding must end at the
  original root, not merely start at it.
- **Literal address controls.** Mutating an outer parent, local position,
  intermediate letter, prefix order, swap flag or inverse residual sign must
  fail the two-level occurrence check. Retain repeated-letter marks as
  distinct addresses. Compose and split both fixtures independently.
- **Ancestry controls.** Omitting the padding edge on an odd path, omitting
  one half of a split occurrence, or silently dropping the final unpaired
  edge must fail. Zero, one, two and three original-edge paths exercise
  the base case and both parity branches.
- **Geometric scope controls.** Keep existing wrong-box, omitted-positional-
  edge, incomplete-table and source/domain-mismatch controls unchanged.
  This theorem converts paths and consumes accepted graph facts; it neither
  reconstructs the graph using a different box nor weakens row completeness.

## Decision, acceptance and retained obligations

**Proceed.** First prove marked composition and the exact incoming root
predecessors; then prove the ancestry inclusion. Prove splitting before
claiming the ordinary rooted-domain iff. An inclusion-only implementation is
still a valid, explicitly narrower extension of nullity. Keep the canonical
native implementation and independent oracle controls source-bound to both
original substitutions, with exact integer arithmetic and full addresses.

Accept only the resulting exact code revision after the complete hosted
Lean source build and compiled transitive axiom audit, plus the prescribed
native/oracle replay and mutation controls. This note is not such acceptance.
The original payload acceptance remains attached to its recorded revision.

Even an ancestry equivalence would concern the specified root-generated
domain. No step proves that every noncomputable `strictPackets` element has
such ancestry. A strict-system obstruction still needs a covered cut set
with positive measure in the same original product space. Nonempty compact
overlaps, physical interval interior, exact mass balance and zero
deficit-overlap products supply no missing positive Haar measure. C4 and the
general Pisot Substitution Conjecture remain unresolved.
