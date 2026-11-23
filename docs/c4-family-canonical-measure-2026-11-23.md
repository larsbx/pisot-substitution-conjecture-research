# Canonical invariant probability for the literal sigma-k shift

## Source decision and scope

**Status:** repository-proved at the source-bound local scope recorded below;
independent human review pending. This is an unpublished review candidate.
The starting revision is
`ce52d46bc4706fd2c15ddd3bb345f6e2067f49cd` of PR #653. Changes remain local until
the requester approves publication.

The target is the literal family `sigma_k = (1, 0 1^k 2, 001)` and its existing
two-sided `C4FamilySymbolicLanguage.SymbolicHull`. For every `k >= 2`, prove
that every shift-invariant Borel probability equals the already defined
`C4FamilySymbolicSpectrum.wordMeasure`. An independently supplied canonical
probability can then be identified by its probability and invariance proofs.
Defining a new name to be `wordMeasure` does not discharge this obligation.

### Targeted literature and infrastructure check

1. Fabien Durand, *Cobham's theorem and substitution subshifts*, Proposition
   11 and Corollaries 12 and 22, proves uniform word frequencies and unique
   ergodicity for primitive substitution subshifts. The conventions in
   Section 2.2 include a prolongable letter and growth of every substituted
   letter. Applying this source literally would require the prolongable
   square, equality of languages, and the bilateral extension. The existing
   positive incidence square proves primitivity, but does not itself prove
   measure uniqueness. [Primary lecture notes](https://cantorsalta2015.sciencesconf.org/conference/cantorsalta2015/Durand.pdf).
2. Mathlib at `4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09` provides Haar-measure
   uniqueness and continuous-test-function measure extensionality. It does
   not contain a primitive-substitution unique-ergodicity theorem in the
   inspected symbolic-dynamics infrastructure.
   [Haar uniqueness source](https://github.com/leanprover-community/mathlib4/blob/4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09/Mathlib/MeasureTheory/Measure/Haar/Unique.lean).
3. The same pinned Mathlib supplies periodic interval-integral identities.
   They give a direct proof that averaging an invariant return-map
   probability over one constant-roof period is invariant under all real
   times.
   [Periodic integration source](https://github.com/leanprover-community/mathlib4/blob/4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09/Mathlib/MeasureTheory/Integral/IntervalIntegral/Periodic.lean).
4. Manibo, Rust and Walton, *Substitutions on compact alphabets*, Journal of
   the London Mathematical Society (2025), Section 5.3, states the invariant
   probability correspondence for a suspension with a roof bounded away
   from zero. For the constant positive roof here, its normalization is
   exactly `mu × Lebesgue|[0,c) / c`. We prove this specialization directly.
   [Published primary source](https://doi.org/10.1112/jlms.70123).
5. Downarowicz and Weiss, *Lifting generic points*, gives a relevant boundary:
   a minimal almost-one-to-one extension of a uniquely ergodic base need
   not be uniquely ergodic. The proof here requires the existing
   **Haar-conull** singleton-fibre set; a merely dense or residual set of
   singleton fibres would not suffice.
   [Published primary source](https://www.cambridge.org/core/journals/ergodic-theory-and-dynamical-systems/article/lifting-generic-points/81E2A366F062E70BC8CC87D291E2AF3E).
6. The existing family proofs already supply a dense real flow on the
   full-history solenoid, a Haar-conull set of singleton fibres, and
   `C4FamilyMeasuredRealization.hullMeasure_eq_of_map`. The last result
   quantifies over arbitrary measures whose solenoid image is Haar. The
   constant-roof strip and its measurable inverse in PR #653 give the exact
   suspension coordinates of the same ordinary legal hull. These are
   repository-proved dependencies, with independent human review pending;
   they are not additional literature assumptions.

**Decision: proceed with a family-specific geometric proof.** Prove that an
arbitrary translation-invariant hull probability projects to Haar, hence
equals `hullMeasure`. Lift an arbitrary invariant return-map probability
using normalized Lebesgue measure on the half-open constant strip. Prove
both translation invariance of this lift and recovery of its base marginal.
Hull uniqueness then forces return-map uniqueness, and the existing actual
word-hull conjugacy transports that equality to the literal shift.

This route avoids a new proof of general primitive-substitution uniform
frequencies. It depends on the already established family singleton-fibre
theorem and retains its `k >= 2` hypothesis. No universal Pisot substitution
conjecture, arbitrary primitive substitution, or `k = 1` conclusion follows.

### Assumptions and hypotheses

All measures use the existing Borel structures on the actual legal spaces.
The arbitrary candidate measure must have mass one and preserve the actual
left shift (or the conjugate next-tile return). The roof is the positive
constant `meanRoof k hk`, with the proved correction and exact strip
identities. Probability normalization, invariance under every real time,
and the base marginal must each be proved explicitly. Continuous-test
measure extensionality is used on the metrizable solenoid, avoiding an
unproved regularity assumption on an arbitrary hull probability.

### Negative controls to retain

- The zero measure is invariant but is not a probability; invariance alone
  cannot establish equality to `wordMeasure`.
- A probability alone does not supply shift invariance.
- Equality of a selected induced measure with a newly introduced alias is
  not uniqueness over arbitrary candidate probabilities.
- The new endpoint must retain the literal family and `k >= 2` and transport
  the existing complex L2 endpoint through an explicit measure equality.

## Derivation / reduction

### 1. Dense solenoid flow determines its probability

Let `Z` be the actual full-history solenoid and let `eta` be any probability
preserved by its real flow. For a bounded continuous real function `f`, the
function

\[
z \longmapsto \int_Z f(z+y)\,d\eta(y)
\]

is continuous. Flow invariance makes it equal to its value at zero on the
proved dense real orbit. Continuity gives the same identity for every `z`.
Bounded-continuous-test extensionality then makes `eta` invariant under
every solenoid translation. Mathlib's compact-group Haar uniqueness and
mass one give `eta = haar`.

The new `solenoidSecondCountable` instance binds the needed topological
hypotheses to the actual solenoid, viewed as a subgroup of the countable
product of three-dimensional tori. No ergodicity premise on `eta` is used.

### 2. Haar-conull singleton fibres determine the hull lift

The existing `hullMeasure_eq_of_map` quantifies over every Borel measure
on the ordinary legal hull whose image under `solenoidRealize` is Haar.
Its proof pulls the existing Haar-conull singleton-fibre set back to a
conull set for the candidate measure and uses the existing measurable
inverse there. Consequently, a candidate with Haar marginal must be the
specified `hullMeasure`.

Combining this with step 1 proves the additional endpoint
`hullMeasure_eq_of_invariant`: every real-translation-invariant hull
probability equals `hullMeasure`, for every `k >= 2`.

### 3. Lift an arbitrary return probability and recover it

Let `mu` be any probability preserved by the actual next-tile return on
the transversal `B`, and put `c = meanRoof k hk > 0`. Define

\[
m_c = c^{-1}\,\mathrm{Leb}|_{[0,c)},\qquad
\Lambda_\mu = \operatorname{strip}_*(\mu\mathbin{\times}m_c).
\]

Lean checks the mass of `m_c` and hence of `Lambda_mu`. The existing
measurable equivalence of the half-open constant strip with the ordinary
hull gives

\[
\operatorname{symbolicFactor}(\operatorname{strip}(b,s))=b
\quad (0\le s<c).
\]

The complement of that interval is null for `m_c`. Mapping the product
through this identity therefore proves exactly
`map_symbolicFactor_suspensionMeasure`: the base marginal of
`Lambda_mu` is the originally supplied `mu`. The base measure is not
defined retrospectively from `hullMeasure` in this argument.

For any bounded continuous real function `f` on the hull, define

\[
F(s)=\int_B f(\operatorname{strip}(b,s))\,d\mu(b).
\]

The exact constant-roof identity and invariance of `mu` under `next` give
`F(s+c)=F(s)`. Boundedness and the finite product measure justify Fubini,
which expresses the integral against `Lambda_mu` as
`c^(-1)` times the integral of `F` over one period. Mathlib's periodic
interval-integral identity makes this average unchanged by every real
translation.

Apply these test-integral identities to continuous solenoid functions
composed with `solenoidRealize`. Equivariance proves that the solenoid
marginal of `Lambda_mu` is flow invariant. Measure extensionality is
performed only on the metrizable solenoid. Steps 1 and 2 give
`Lambda_mu = hullMeasure`. Recovering the base marginal then gives
`mu = symbolicMeasure`. This proves uniqueness without assuming a
disintegration formula for an arbitrary hull measure.

### 4. Transfer to all actual legal words, then transfer spectrum

The existing `itineraryHomeomorph` is a conjugacy between the transversal
and all two-sided legal words. Pull an arbitrary invariant word probability
back through its measurable inverse, apply return-map uniqueness, and push
the equality forward. This gives the explicit equality to `wordMeasure`.

The spectral transport theorem takes that measure equality as a separate
argument. Substitution of equal measures identifies the two complex `L2`
spaces; proof irrelevance identifies the proofs of measure preservation.
The original `C4FamilySymbolicSpectrum.pureDiscrete_shift` is then applied
without changing its statement or proof.

## Checked theorem statements

The namespace of the first statement is
`Psc.C4FamilySymbolicMeasureUniqueness`:

```lean
theorem invariant_probability_eq_wordMeasure
    (k : ℕ) (hk : 1 ≤ k) (hk₂ : 2 ≤ k)
    (μ : Measure (SymbolicHull k hk)) [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (shift (k := k) (hk := hk)) μ μ) :
    μ = wordMeasure k hk hk₂
```

The following statements are in `Psc.C4FamilyCanonicalSpectrum`:

```lean
theorem existsUnique_invariant_probability
    (k : ℕ) (hk : 1 ≤ k) (hk₂ : 2 ≤ k) :
    ∃! μ : Measure (SymbolicHull k hk),
      IsProbabilityMeasure μ ∧
        MeasurePreserving (shift (k := k) (hk := hk)) μ μ

theorem pureDiscrete_shift_of_measure_eq
    (k : ℕ) (hk : 1 ≤ k) (hk₂ : 2 ≤ k)
    (μ : Measure (SymbolicHull k hk))
    (hμ : MeasurePreserving (shift (k := k) (hk := hk)) μ μ)
    (hEq : μ = wordMeasure k hk hk₂) :
    (Submodule.span ℂ {v : Lp ℂ 2 μ |
      v ≠ 0 ∧ ∃ z : ℂ,
        Lp.compMeasurePreserving (shift (k := k) (hk := hk)) hμ v = z • v}
    ).topologicalClosure = ⊤
```

These statements expand the source's section parameters. The same namespace's
`pureDiscrete_shift_of_invariant_probability` replaces the equality
hypothesis with `[IsProbabilityMeasure mu]` and derives the equality by
the first theorem. The arbitrary measure, actual shift and `k >= 2`
binder are all part of the independently checked endpoint contracts.

## Established family hypotheses and source dependencies

The existing exact incidence results are

\[
M_k=\begin{pmatrix}0&1&2\\1&k&1\\0&1&0\end{pmatrix},\qquad
M_k^2=\begin{pmatrix}1&k+2&1\\k&k^2+2&k+2\\1&k&1\end{pmatrix}.
\]

Every square entry is positive for `k >= 1`. The existing
`ParameterFamilyPisot.primitive` binds this to the literal substitution,
and `every_letter_in_square` binds it to actual supertile occurrence.
`PrimitiveExpansion` supplies nonerasing and an expanding power; `Incidence` supplies
exact letter-count/matrix correspondence. The symbolic language uses
every finite block at every integer position, with existence of a literal
supertile occurrence. No sampled language or finite census replaces it.

| Dependency | Exact role and parameter range |
| --- | --- |
| `ParameterFamilyPisot.primitive` and `ParameterFamilyTiling.every_letter_in_square` | Existing literal positive-square and occurrence facts, `k >= 1`; used by the inherited language/geometry construction. |
| `C4FamilySymbolicLanguage.itineraryHomeomorph` and `itineraryHomeomorph_next` | Actual bilateral legal carrier and shift conjugacy, `k >= 1`. |
| `C4FamilySymbolicSection.meanRoof_pos`, `translate_mean_strip`, `strip_injOn`, `exists_strip` | Positive constant roof and exact coordinates, `k >= 1`. |
| `C4FamilySymbolicSpectrum.constantStripEquiv` | Measurable half-open coordinates and inverse, `k >= 1`. |
| `PeriodicPartnerRealizationOnto.denseRange_flow_zero` with `ParameterFamilySolenoid.pisotData` | Dense flow on the actual full-history solenoid, `k >= 1`. |
| `C4FamilyHaarSingletonFibres.exists_conull_singleton_fibres` and `C4FamilyMeasuredRealization.hullMeasure_eq_of_map` | Haar-conull singleton fibres and uniqueness of their arbitrary measure lift, `k >= 2`. |
| `C4FamilySymbolicSpectrum.measurePreserving_wordShift` | Existing existence witness for the invariant symbolic probability, `k >= 2`. |
| `C4FamilySymbolicSpectrum.pureDiscrete_shift` | Unchanged complex `L2` spectrum for induced `wordMeasure`, `k >= 2`. |
| Pinned Mathlib Haar uniqueness, finite-measure extensionality, product integration and periodic interval integration | General checked measure-theoretic steps; no primitive-substitution unique-ergodicity axiom is introduced. |

The finite-kernel infrastructure remains a dependency of the existing
family geometry and coincidence proofs. No new numerical census,
finite cutoff or general uniform word-frequency claim is needed here.

## Evidence and replay

The toolchain is Lean `4.34.0-rc2`, compiler commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`, with Mathlib
`4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09` and the unchanged dependency
manifest from PR #653.

The local scoped build and canonical audit passed. They checked **3 new
modules, 45 owned declarations, 25 theorem constants, 8 exact endpoint
contracts and 22 controls**. The recursive axiom closure is limited to
`propext`, `Classical.choice` and `Quot.sound`. The Lake run reports 3,186
dependency jobs; this is not a count of project modules or new theorems.

The evidence packet records the isolated family replay, final source
digests, original and new endpoint audit logs, governance checks and
revision identity. Historical hosted evidence of the starting revision
is kept separate: its [family spectral run](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/45087039840)
passed, while [Physical Mass](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/45087039867)
failed. Neither run validates these new unpublished sources.

From the repository root:

```sh
python3 tools/make_proof_bank.py --check
tools/check_c4_parameter_family.sh
PYTHONPATH=tools python3 -m claim_governance.cli --root .
python3 -m pytest tests/test_proof_bank.py tests/test_recorded_data_integrity.py
python3 tools/check_markdown_source.py
git diff --check
```

The family gate builds the new modules from its isolated source-only
workspace and requires each new endpoint exactly once, all three owned
modules, the exact 45/25 declaration/theorem tally and all 22 controls.
The narrower new-endpoint replay from `proof/PscVerif` is:

```sh
lake --no-cache build PscVerif.C4FamilyCanonicalSpectrum
lake --no-cache env lean -DautoImplicit=false -Dpp.unicode.fun=true \
  C4FamilyCanonicalMeasureAudit.lean
```

### Negative controls actually checked

The audit proves that the zero measure is invariant but is not a
probability and differs from `wordMeasure`. For every actual legal word,
its Dirac mass is a probability but is not shift invariant: itinerary
conjugacy would turn a fixed word into a nonzero real tiling period,
contradicting the existing aperiodicity theorem and positive roof.

The contract recognizer separately rejects omission of normalization,
omission of invariance and omission of `k >= 2`, plus absent or wrongly
typed declarations for every endpoint. The `k = 1` refusal preserves this
proof's scope; it is not a claim that unique ergodicity fails there.

## Non-claims / remaining gaps

For `k >= 2`, uniqueness of the invariant probability on the existing
literal legal symbolic hull is now formalized. Thus an independently
defined canonical Borel probability on that same carrier is identified
as soon as its probability and shift-invariance proofs are supplied.
There was no independently defined canonical measure object in the
starting Lean source, and this change creates no alias pretending to
be such an independent construction.

A separate cylinder-frequency construction and general primitive-
substitution unique-ergodicity theorem are not added. They are unnecessary
for the proved family equality. The physical variable-roof Lebesgue
disintegration formula remains a written statement; the normalized
**corrected constant strip** lift and its equality to `hullMeasure` are
proved here. The separately published `k = 1` result is not incorporated
into these `k >= 2` endpoints.

The universal PSC, BH, residual A1-prime and general C4 investigations
retain their own obligations. No theorem here quantifies over arbitrary
Pisot substitutions. Independent human validation of the entire inherited
chain remains pending, and publishing these local changes requires the
requester's approval.
