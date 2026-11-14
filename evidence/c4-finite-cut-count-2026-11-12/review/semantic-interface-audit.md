# Independent finite cut-count interface audit

Read-only semantic inspection, 2026-11-12. Subject: existing PR #560,
`/workspace/scratch/f96c28a561ad/psc-count`, commit
`31f8046291f2428e839d95e8890c8342858ec210`, tree
`e38c3f65efb79fa72860d8ef222e96695847a551`. The checkout was clean at inspection.
No repository edits, tests, builds, remote actions, or compiler acceptance
claims were made by this audit.

## Decision

**No mathematical or theorem-scope blocker found in the two actual modules.**
They implement the central finite interface previously proposed in
`compact-next-count-interface-review.md`: count distinct original integer
vectors at complete reduction starts, obtain full actual balanced marks,
bound total physical length, place the vectors in the correct half-open
strip, and capture their images in the represented-carrier open neighborhood.

PR #560 already owns this implementation. Do not start a duplicate module
or expand its scope merely to follow the older plan. Completion of the
required source-bound build/audit, evidence, and governance is separate
from this semantic assessment. No focused compilation result was treated
as the complete gate.

The audit also read `AGENTS.md`, relevant recent entries of
`docs/side-notes-ledger.md`, and the previous interface review. In particular,
the ledger's noninjective reference-witness warning and its distinction
between open capture and a lattice count remain respected.

## Source binding and ownership

| File | SHA256 |
| --- | --- |
| `proof/PscVerif/PscVerif/StrictCutCount.lean` | `465d1ad883556eca80db059bde0564a425a6a62407cd307d728347bc558d62b1` |
| `proof/PscVerif/PscVerif/NamedCutCount.lean` | `9e265aa7f9a9a4cf4dbef2a2f4f1a320740f8cc19a6d290679d6ec8343cfeae4` |
| `docs/c4-finite-cut-count.md` | `46e7b6f53c6b5e4e096e646511c28b8bf55024b00f3b3faa3252f9aa6421e33b` |

The current split is appropriate. `StrictCutCount` owns integer starts,
word reconstruction, generic counting and strip bounds. `NamedCutCount`
owns the authentic substitutions, exact power scaling, strict-carrier
closure, and the existing compact-neighborhood consumer. There are nine
public theorem declarations, three private proof helpers, and three
definitions across these files. Private helpers should not be confused
with additional public contracts or with compiler-generated constants.

Parallel completion can keep semantic review, evidence/axiom inspection,
and documentation/governance independent. No mathematical author needs
to rewrite a module already supplied by this PR. Any later analytic count
belongs in a separate module consuming this integer interface.

## Exact public contracts and proof checks

### Integer starts and occurrence identity

`factorStart bs : Fin bs.length → (Fin 3 → ℤ)` is the Parikh vector of
the flattened top tracks before the selected factor. `startVectors bs`
is its `Finset.univ.image`.

`factorStart_injective` assumes exactly
`∀ B ∈ bs, B.1 ≠ []`. It proves strict monotonicity of ordinary prefix
length on `Set.Iic bs.length`, using `List.take_add_one` and the positive
length of each selected top factor. Equality of Parikh vectors gives
`Equiv1`, hence equal ordinary word lengths; injectivity follows.

This is the required argument on **original starts**. It does not assume
balance, positive physical weights, rational independence, or injectivity
of a geometric projection. The use of `Fin bs.length` avoids the false
claim that `take j` remains injective after the list ends.

`card_startVectors` applies the proved injection to the finite image and
obtains `(startVectors bs).card = bs.length`. Occurrences remain separate
when factor labels repeat. No `List.toFinset` of factor labels intervenes.

### Full actual marks and balanced prefixes

`exists_balanced_marks_of_mem` assumes `Equiv1 u v` and membership in
`startVectors (red u v)`. It returns `top : Mark u` and `bottom : Mark v`
whose before-vectors both equal the supplied original integer vector.

The private `markAtFactorStart` reconstructs the selected letter and full
suffix using `List.take_append_drop` and `List.drop_eq_getElem_cons`.
The suffix includes both the remainder of the selected factor and all
later factors. It therefore supplies genuine `Mark.split` equations,
not truncated prefix witnesses. `red_isBlock` supplies top nonemptiness;
balance of the selected factor gives bottom nonemptiness.

`Binomial.equiv1_join` on the preceding factors supplies prefix balance.
Finally `red_top hbal.length_eq` and `red_bot hbal.length_eq` transport
the full marks from the concatenated factors to the original words. The
direction of each identity and of the bottom Parikh equality is correct.

The result is an inclusion into actual proper balanced cuts. It does not
claim an exhaustive equivalence with every balanced cut, and no such
equivalence is needed for the lower bound.

### Finite physical bound and strip

`physicalLength_le_card_reduction_starts ℓ L` assumes precisely:

```text
hbal   : Equiv1 u v
hbound : ∀ B ∈ red u v, physicalLength ℓ B.1 ≤ L.
```

Its conclusion is
`physicalLength ℓ u ≤ L * ((startVectors (red u v)).card : ℝ)`.
The private list induction sums the given upper bound, and exact
cardinality replaces the number of factors. This argument is valid for
arbitrary real weights and arbitrary real `L`; no positivity premise is
missing. The theorem does not enlarge the counted set. If a later caller
does so, it must supply `0 ≤ L` for monotone multiplication.

`offset_mem_strip_of_mem` explicitly assumes `∀ a, 0 < ℓ a` in addition
to balance and start membership. It uses the actual top mark and the
identity `offset ℓ (parikhZ top.before) = physicalLength ℓ top.before`.
Nonnegative prefix length gives the lower bound; the selected positive
letter and nonnegative suffix give the strict upper bound. The strip is
exactly `0 ≤ offset ℓ z < physicalLength ℓ u`, with the original origin.

This chosen global positive-row premise is stronger than factor-level
positivity but explicit and sufficient for every intended named use. It
does not weaken an earlier contract or assume a measure conclusion.

### Named count, scaling, carrier, and threshold

`integerStarts fixture n T` is exactly the generic start set of the
complete reduction of the two original words at power `12*n`.

`integerStarts_count_and_strip` takes a literal `StrictSystem`, a real
bound `L` with `∀ B ∈ C, physicalLength physicalRow B.1 ≤ L`, and `T ∈ C`.
It uses `Descendants.equiv1_iterate_subst` and
`StrictSystem.mem_of_red_iterate`; no factor is omitted from closure.
The private whole-word scaling induction uses
`NamedGeometricEnclosure.physicalLength_subst` and gives the precise
length `beta^(12*n) * physicalLength physicalRow T.1`. Thus the count
and strip refer to the same `integerStarts` definition and physical scale.

`eventually_integerStarts_mem` fixes the fixture, finite carrier, strict
witness, and open neighborhood before selecting `N`. Its conclusion is

```text
∃ N, ∀ n ≥ N, ∀ T ∈ C, ∀ z ∈ integerStarts fixture n T,
  ambientStar (substitution fixture) piZ z ∈ U.
```

The premise is `carrierOverlap fixture C ⊆ U`, the union indexed by
actual `CutPair C`, not the larger all-distinct union. The existing
`eventually_carrierOverlap_strict_cuts_mem` authenticates represented
labels through `strict_cut_labels`; the new module supplies its genuine
balanced marks. `StablePrefixWindow.subst_iterateImages` rewrites the
literal inflated word types without changing the original product carrier.
The equality `ht.trans hb.symm` has the correct top-to-bottom orientation.

One `N` controls every source in the fixed `C` at every later generation.
Different members may be selected at different generations; an expanding
source family is not admitted. The physical length may depend on `T`.
No ambient image cardinality or reference-witness injectivity is asserted.

## Boundary cases and independent controls

| Case | Current behavior / assessment |
| --- | --- |
| Empty factor list or empty balanced words | `Fin 0` has no starts; `empty_startVectors` proves the empty set. The count is `0 ≤ 0`; mark and strip assertions are vacuous. |
| Initial versus terminal endpoint | For a nonempty list, ordinal zero gives the zero vector. `Fin bs.length` excludes the terminal ordinal. Full marks independently certify that every counted start has a following letter. |
| Repeated factor labels | `repeated_factor_control` checks two equal labels still give two starts. Its factors `([0],[1])` are not balanced; this exercises the generic nonempty-top injection, not the reduction or strict-carrier adapter. The control is valid at that scope. |
| Zero-length factors | The generic injection explicitly rejects them. For example, two empty top factors would map both ordinals to zero. No current theorem permits that false extension. |
| Erasing substitution | Raw `StrictSystem` does not imply nonerasure. Empty inflated words would correctly give zero count and vacuous marks/strip. The named result uses its specific substitutions and exact positive scaling; it does not derive nonerasure from strictness alone. |
| Empty carrier | Impossible under `StrictSystem.nonempty`. Generic list statements remain valid on the empty list. No undefined maximum over an empty carrier is introduced. |
| Nonpositive letter weights | The general sum bound remains valid. The strict strip theorem requires positive weights; zero weights would make the asserted strict upper bound false. |
| Negative bound and a larger cut set | There is no enlargement theorem here. Multiplying a cardinality inequality by a negative bound would reverse it; later consumers must use nonnegativity. |

Optional stronger controls could exercise a repeated **balanced reduction**
such as `([0,1],[1,0])` twice, explicitly refute injection with an empty
top factor, and refute the strict strip after replacing the positive row
by zero. These would add boundary coverage, not repair a statement defect.
They were not implemented or tested during this audit.

## Missing obligations versus optional refinements

**No missing finite premise was concealed.** The carrier bound `hL` is
explicit. A separately packaged positive maximum is a useful future
convenience, not a blocker: set
`Lmax := C.sup' strict.nonempty (fun B => physicalLength physicalRow B.1)`.
`Finset.le_sup'` supplies the bound; positivity follows by choosing a
member, using `strict.isBlock` and the positive row. This would remove an
assembly step for a later consumer, but the present theorem correctly
accepts any valid bound. The documentation's finiteness observation is
mathematically valid and does not claim a separately compiled maximum lemma.

Likewise, a public whole-word scaling lemma, a theorem `X_n → ∞`, and an
integer-start finite-open-subcover corollary can be added when a consumer
needs them. The existing private scaling proof and public open-capture
theorem already suffice for the advertised result. There is no reason to
replace the short sum induction: the available alternative is
`List.sum_le_length_nsmul` (`sum_le_card_nsmul` is a deprecated alias).

The remaining substantive mathematics is the fixed-origin upper count of
the **integer** strip/window set, its finiteness for bounded stable windows,
all-depth cylinder masses, actual chart covolume, and regular outer-cover
measure assembly. An arbitrary open `U` need not have finite occupancy.
`PhysicalMass` and existing mismatch-position counts do not supply these
claims. The inspected documentation preserves this analytic boundary and
does not promote M1, positive overlap measure, C4, or PSC.

This audit supplies semantic review only. Acceptance belongs to the exact
source-bound terminal build/audit receipts and their separate inspection.
