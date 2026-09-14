------------------------------- MODULE Ledger -------------------------------
(***************************************************************************)
(* Live proof-dependency ledger for the PSC balanced-pair program.          *)
(*                                                                         *)
(* A named result can itself be a conditional theorem. For example,        *)
(* ParikhIntertwiner means: for every finite closed nonproductive SCC,      *)
(* P N = M P ... . Such a theorem does not require global G1 merely        *)
(* because its premise mentions a finite closed SCC. G1 is required at the *)
(* separate SinkSCCReduction step that extracts such an SCC from global     *)
(* nonproductivity.                                                         *)
(*                                                                         *)
(* The 2026-09-11 architecture has two independent open gates:             *)
(*   G1b-2 renewal finiteness (Level 2; G1b-1 bounded discrepancy was       *)
(*   reconstructed and proved on 2026-09-13, so G1 <=> G1b-2), and          *)
(*   concentration / aux-B and wedge productivity (Level 3 under G1);      *)
(*   the latter is the final step inside SpanRichProductivity below.       *)
(* Former v16/later status claims are resolved claim by claim: reconstructed *)
(* theorems are included in ProvedDef, while concentration and realization   *)
(* obligations remain open inputs. Missing-v16 status is provenance metadata. *)
(*                                                                         *)
(* 2026-09-13: the merged manuscript                                        *)
(*   manuscripts/PSC_balanced_pair_state_2026-09-13.tex                     *)
(* proves a wedge dichotomy (its Proposition 5.20) under which              *)
(* ConcentrationAuxB is equivalent to "no strict component with K2 = 0"     *)
(* and SpanRichProductivity's final step is equivalent to "no strict        *)
(* component with K2 /= 0". Both stay outside ProvedDef; the dependency     *)
(* graph below is unchanged.                                                *)
(*                                                                         *)
(* C4 -> C3Local -> C2 -> SCCProducer remains encoded only as one           *)
(* sufficiency route. No converse implication is asserted.                  *)
(***************************************************************************)
EXTENDS ProofArchitecture

ResultSet == {
    \* --- symbolic side, repository theorem-grade -------------------------
    "DefectTheorem",
    "UniqueDecodability",
    "UDForPowers",
    "LocalWitnessInjectivity",
    "MassBalanceK2Obstruction",
    "AlgebraicEmbedding",
    "WedgeBound",

    \* --- seed spectral module --------------------------------------------
    "PhiSemisimplicity",
    "ThetaIntertwining",
    "SeedCentralizer",
    "Target1",
    "DominantCubicCapture",
    "SpectralBlackBox",

    \* --- v33 / v34 historical route -------------------------------------
    "InterBlockCancellation",
    "DominantK2Source",
    "LoadBearingSCC",

    \* --- live graph / C3-C4 reductions ----------------------------------
    "SinkSCCReduction",
    "C3Locality",
    "EndpointCore",
    "GlobalEndpointSync",
    "SignatureReduction",
    "ParikhIntertwiner",
    "OrientationMonodromy",
    "OrientationSpectrum",
    "DefectIntertwiner",
    "W3LowGrowth",
    "Degree4Floor",
    "Mod3Sieve",
    "ParitySieve",
    "MidArea",
    "MeanAreaLift",
    "LatticeLift",

    \* --- 2026-09-11 Level-2 gate ----------------------------------------
    "G1b1BoundedDiscrepancy",
    "G1b2RenewalFiniteness",
    "G1FromRenewal",

    \* --- 2026-09-13 overlap route (finite graph, no G1) -----------------
    "SwapOverlapFiniteness",
    "OverlapFullRank",
    "OverlapProductivity",
    "CoincidenceDensityOne",
    "AllStatesProductiveViaOverlaps",
    "DensityToPDSBridge",
    "PDSOverlapRoute",
    "AlignedOverlapsAreStrongCoincidence",
    "BoundaryCoincidenceCriterion",

    \* --- 2026-09-11 strongest Level-3 spectral route ---------------------
    "ConcentrationAuxB",
    "GaloisWedgePropagation",
    "SpanRichProductivity",
    "SpectralSCCProducer",
    "PDSSpectralRoute",

    \* --- open C4 sufficiency route --------------------------------------
    "C4",
    "C3Local",
    "C2",
    "G1",
    "SCCProducer",
    "PDS",

    \* --- literature / repository BPA bridge -----------------------------
    "StandardBPAEquivalence",
    "RepoSeedUnionBridge",
    "PDSImpliesRepoG1",

    \* --- retracted -------------------------------------------------------
    "V5Thm51"
}

RequiresDef == [r \in ResultSet |->
    CASE r = "DefectTheorem"            -> {}
      [] r = "UniqueDecodability"       -> {"DefectTheorem"}
      [] r = "UDForPowers"              -> {"UniqueDecodability"}
      [] r = "LocalWitnessInjectivity"  -> {}
      [] r = "MassBalanceK2Obstruction" -> {}
      [] r = "AlgebraicEmbedding"       -> {"UniqueDecodability"}
      [] r = "WedgeBound"               -> {"AlgebraicEmbedding", "MassBalanceK2Obstruction"}

      [] r = "PhiSemisimplicity"        -> {}
      [] r = "ThetaIntertwining"        -> {}
      [] r = "SeedCentralizer"          -> {"ThetaIntertwining", "PhiSemisimplicity"}
      [] r = "Target1"                  -> {"SeedCentralizer"}
      [] r = "DominantCubicCapture"     -> {"Target1"}
      [] r = "SpectralBlackBox"         -> {"Target1", "DominantCubicCapture"}

      [] r = "InterBlockCancellation"   -> {}
      [] r = "DominantK2Source"         -> {}
      [] r = "LoadBearingSCC"           -> {"G1", "DominantK2Source", "InterBlockCancellation"}

      (* Conditional-on-FCS structural theorems carry that premise inside
         their mathematical statement; they do not require global G1 here. *)
      [] r = "SinkSCCReduction"         -> {"G1"}
      [] r = "C3Locality"               -> {}
      [] r = "EndpointCore"             -> {}
      [] r = "GlobalEndpointSync"       -> {"EndpointCore"}
      [] r = "SignatureReduction"       -> {"EndpointCore"}
      [] r = "ParikhIntertwiner"        -> {}
      [] r = "OrientationMonodromy"     -> {}
      [] r = "OrientationSpectrum"      -> {"OrientationMonodromy", "ParikhIntertwiner"}
      [] r = "DefectIntertwiner"        -> {"OrientationMonodromy"}
      [] r = "W3LowGrowth"              -> {"DefectIntertwiner", "PhiSemisimplicity"}
      [] r = "Degree4Floor"             -> {"DefectIntertwiner"}
      [] r = "Mod3Sieve"                -> {"DefectIntertwiner"}
      [] r = "ParitySieve"              -> {"DefectIntertwiner"}
      [] r = "MidArea"                  -> {}
      [] r = "MeanAreaLift"             -> {"MidArea", "ParikhIntertwiner"}
      [] r = "LatticeLift"              -> {"MeanAreaLift"}

      (* Level 2: G1b1 is repository-proved by the independent reconstruction
         docs/source-imports/issue-45/g1b1-bounded-discrepancy-reconstruction.md
         (manuscript Theorem 4.4); it uses only primitivity and the Pisot
         spectrum, not UniqueDecodability. G1b2 is the open input. The
         assembly G1FromRenewal and G1 itself are conditional theorems. *)
      [] r = "G1b1BoundedDiscrepancy"    -> {}
      [] r = "G1b2RenewalFiniteness"     -> {"G1b1BoundedDiscrepancy"}
      [] r = "G1FromRenewal"             -> {"G1b1BoundedDiscrepancy", "G1b2RenewalFiniteness"}
      [] r = "G1"                        -> {"G1FromRenewal"}

      (* Overlap route (docs/overlap-finiteness-and-coincidence-density-
         2026-09-13.md; manuscript Theorem 4.22 and Theorem 5.32). The seed-patch overlap graph is finite by bounded
         discrepancy. OverlapProductivity is the open Level-3 statement in
         G1-free form and the only open input of this route; it implies
         productivity of every reachable state
         (AllStatesProductiveViaOverlaps) with no finiteness hypothesis, and
         a G1-based PDS assembly remains available. CoincidenceDensityOne
         records the proved overlap-productivity equivalence, and
         DensityToPDSBridge is the imported Barge-Stimac-Williams theorem
         (proved), so PDSOverlapRoute is conditional on OverlapProductivity
         alone. *)
      [] r = "SwapOverlapFiniteness"      -> {"G1b1BoundedDiscrepancy"}
      (* Manuscript Corollary 5.34: a child-closed set of non-coincidence
         overlaps has full-rank intersection vectors, so spec(M) lies in the
         spectrum of its child-count matrix. A constraint, not an exclusion. *)
      [] r = "OverlapFullRank"            -> {}
      [] r = "OverlapProductivity"        -> {}
      [] r = "CoincidenceDensityOne"      -> {"OverlapProductivity", "SwapOverlapFiniteness"}
      [] r = "AllStatesProductiveViaOverlaps" -> {"OverlapProductivity", "SwapOverlapFiniteness"}
      (* Imported: Barge-Stimac-Williams Theorem 3.1 (density-one -> dense
         good set -> PDS; manuscript Lemma 5.36, Imported Theorem 5.37,
         Theorem 5.38). No finiteness hypothesis. *)
      [] r = "DensityToPDSBridge"         -> {}
      [] r = "PDSOverlapRoute"            -> {"CoincidenceDensityOne", "DensityToPDSBridge"}
      (* Manuscript Proposition 5.39: the offset-zero and right-aligned
         overlaps are seed overlaps, productive iff the letter pair is
         eventually coincident (prefix / suffix); so OverlapProductivity
         contains the two-sided strong coincidence condition (open, d >= 3).
         Proposition 5.40 / Corollary 5.41: boundary coincidence at level m
         iff M^m w is a difference of proper-prefix Parikh vectors iff an
         offset-zero descendant exists; under strong coincidence
         OverlapProductivity is this hitting statement. Both are
         unconditional theorems and constrain, not close, the gate. *)
      [] r = "AlignedOverlapsAreStrongCoincidence" -> {}
      [] r = "BoundaryCoincidenceCriterion" -> {}

      (* Historical name retained for compatibility. The carrier span result
         is now repository-proved by the wedge dichotomy; it needs no separate
         source-pending Galois theorem. Concentration and productivity remain
         open and separate. *)
      [] r = "ConcentrationAuxB"         -> {"G1", "SinkSCCReduction"}
      [] r = "GaloisWedgePropagation"   -> {}
      [] r = "SpanRichProductivity"     -> {"ConcentrationAuxB", "GaloisWedgePropagation"}
      [] r = "SpectralSCCProducer"      -> {"G1", "SinkSCCReduction", "SpanRichProductivity"}
      [] r = "PDSSpectralRoute"         -> {"G1", "SpectralSCCProducer"}

      (* Supporting boundary/C4 route. *)
      [] r = "C4"                       -> {}
      [] r = "C3Local"                  -> {"C4", "C3Locality"}
      [] r = "C2"                       -> {"C3Local"}
      [] r = "SCCProducer"              -> {"G1", "SinkSCCReduction", "C2"}
      [] r = "PDS"                      -> {"G1", "SCCProducer"}

      (* Literature theorem and repository-side seed-union lemma are proved
         separately. The final seedwise PDS=>repo-G1 implication remains open. *)
      [] r = "StandardBPAEquivalence"   -> {}
      [] r = "RepoSeedUnionBridge"      -> {}
      [] r = "PDSImpliesRepoG1"         -> {"StandardBPAEquivalence", "RepoSeedUnionBridge"}

      [] r = "V5Thm51"                  -> {}]

ProvedDef == {
    "DefectTheorem", "UniqueDecodability", "UDForPowers",
    "LocalWitnessInjectivity", "MassBalanceK2Obstruction", "AlgebraicEmbedding",
    "WedgeBound", "PhiSemisimplicity", "ThetaIntertwining", "SeedCentralizer",
    "Target1", "DominantCubicCapture", "SpectralBlackBox",
    "InterBlockCancellation", "DominantK2Source", "LoadBearingSCC",

    "SinkSCCReduction", "C3Locality", "EndpointCore", "GlobalEndpointSync",
    "SignatureReduction", "ParikhIntertwiner", "OrientationMonodromy",
    "OrientationSpectrum", "DefectIntertwiner", "W3LowGrowth",
    "Degree4Floor", "Mod3Sieve", "ParitySieve", "MidArea",
    "MeanAreaLift", "LatticeLift",

    (* Independently reconstructed as the wedge dichotomy: nonzero K2 on a
       closed nonproductive carrier spans the full rational wedge space. *)
    "GaloisWedgePropagation",

    (* G1b1 is proved (2026-09-13 reconstruction). G1FromRenewal is the
       assembly theorem; G1b2, the remaining gate input, is intentionally
       absent, so G1 stays unreachable without assumptions. *)
    "G1b1BoundedDiscrepancy", "G1FromRenewal", "G1",

    (* Overlap route: graph finiteness and the conditional assembly theorems
       are proved, and the density-to-PDS bridge is imported. OverlapProductivity
       is the only absent input, so PDS stays unreachable without assumptions. *)
    "SwapOverlapFiniteness", "OverlapFullRank", "CoincidenceDensityOne",
    "AlignedOverlapsAreStrongCoincidence", "BoundaryCoincidenceCriterion",
    "AllStatesProductiveViaOverlaps", "DensityToPDSBridge", "PDSOverlapRoute",

    (* Boundary route conditional reductions remain proved. C4 itself is absent. *)
    "C3Local", "C2", "SCCProducer", "PDS",

    (* PDSSpectralRoute is a conditional assembly statement, but the open
       spectral carrier inputs keep it unreachable on main. *)
    "PDSSpectralRoute",

    "StandardBPAEquivalence", "RepoSeedUnionBridge"
}

WithdrawnDef == {"V5Thm51"}

NoAssumptions == {}
G1AndProducer == {"G1", "SCCProducer"}
G1Only == {"G1"}
G1AndC4 == {"G1", "C4"}

(* Explicit hypothetical completion assumptions for future model checks. *)
RenewalGateAssumed == {"G1b1BoundedDiscrepancy", "G1b2RenewalFiniteness"}
SpectralGateAssumed == {"G1", "ConcentrationAuxB", "SpanRichProductivity", "SpectralSCCProducer"}
OverlapGateAssumed == {"OverlapProductivity"}
=============================================================================
