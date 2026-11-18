# Named strict-system exclusion: pre-code source decision

Decision recorded before the new proof and exporter edits, on parent
`64a304b1e753624b0e39b57d2c00cf2139ef9a85`.

## Proposed claim

For either literal substitution `1/021/001` or `1/012/001`, compose the
positive-measure consequence of a supplied finite `StrictSystem` with the
kernel-checked nullity of the three original zero-offset root overlaps.
Derive absence of such a strict system, without a bound on its number of
states. The substitution parameter remains `Fin 2`.

The immediate consumer retains the same normalized additive Haar measure
on the original compatible-sequence carrier throughout. A statement without
that measure argument requires an explicit normalized Haar existence
construction; existence must not be erased from the theorem's type.

## Targeted primary-source check

1. **Minervino and Thuswaldner, *The geometry of non-unit Pisot
   substitutions*, Ann. Inst. Fourier 64 (2014), 1373–1417,
   [doi:10.5802/aif.2884](https://www.numdam.org/articles/10.5802/aif.2884/).**
   The retrieved primary-source section 3 excerpt defines the internal
   representation space with its product measure; Lemma 3.1 gives the
   product-formula scaling. This is the closest geometric setting. The
   present composition uses the repository's already authenticated literal
   tiles and original matrix-adic factor. No tiling, coincidence, or
   all-substitution conclusion from the paper is imported as a premise.
   The article record and indexed section excerpt were available; direct
   PDF retrieval was denied, so no fresh full-paper review is asserted.
2. **Mathlib, [OuterMeasure.Basic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/OuterMeasure/Basic.html).**
   `measure_mono_null` and `measure_iUnion_null` express the standard
   null-subset and countable-null-union facts. The repository's existing
   `OverlapContraction.no_positive_subset_of_null` already combines their
   finite form with strict positivity. Reuse that result. This step does
   not require disjointness or an unproved measure-equals-cardinality rule.
3. **Mathlib, [Group.Measure](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Group/Measure.html).**
   Product translation-invariance and `Measure.IsAddHaarMeasure` are
   explicit interfaces. Both repository inputs use precisely
   `(volume : Measure Stable).prod nu`; `NamedFundamentalCell.internalMeasure`
   abbreviates this expression. No new chart-volume normalization enters
   the comparison. Compilation uses the pinned Mathlib revision
   `4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09`, not the live documentation.
4. **Existing source-bound repository proofs.**
   `StrictSystem.cutPair_ne` supplies distinct labels;
   `ArchivedGraphRefinement.archivedRoot` lists exactly `01`, `02`, `12`
   with displacement zero; `ArchivedPayload.Packet.roots_null` binds their
   nullity to the accepted original positional payload. The positivity
   source is `NamedPositiveOverlap.carrierOverlap_measure_pos`. Its full
   repaired-head acceptance is still pending at this decision. It may be
   used provisionally for development, but receives no completed-gate
   credit until the combined build succeeds.

## Hypotheses and boundaries

Unpack `carrierOverlap` into actual `CutPair` labels. Distinct labels on
the three-letter alphabet select one of the three archived roots; reversed
label order uses intersection commutativity. This set equality is valid
because the displacement is zero. At nonzero displacement, swapping tracks
translates an overlap and does not in general preserve the set.

Root coverage is sufficient. This proof does not require identifying the
archive with all `strictPackets`, extending even ancestry to odd ancestry,
or establishing a new per-pair frequency theorem. A null set need not be
empty: contradiction uses the positive measure forced by strictness.

## Controls and acceptance

- A diagonal singleton tile has positive counting measure even when all
  distinct-letter root intersections are null. Distinctness is essential.
- If only the `01` and `02` roots are checked, the `12` intersection may
  have positive measure. All three roots are essential.
- Preserve literal-source, positional multiplicity, archive-identity and
  transitive-axiom checks. Add an exact-type check for each generated
  exclusion theorem and refuse a right-name proof of a weaker proposition.
- Compile the repaired positivity module and new consumer together. Then
  replay both actual generated payloads through the unchanged isolated
  full-build gate, extended semantic auditor, and independent packet oracle.

## Decision

**Proceed with the two-fixture composition.** Finite null-union reasoning
is standard; the contribution is binding the positive and null measures
to the same literal tiles, root packets, and checked archive. General C4,
G1, pure discrete spectrum and PSC retain their existing status. Independent
human review remains separate validation debt.
