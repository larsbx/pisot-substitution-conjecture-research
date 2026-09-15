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
(* The shortest current PDS route has one open premise: OverlapProductivity. *)
(* G1b-2 and the spectral carrier obligations remain stronger parallel      *)
(* theorem programmes. Supporting overlap reductions may constrain the open *)
(* gate while remaining in ProvedDef without making it reachable.          *)
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

    \* --- overlap route (finite graph, no G1) -----------------------------
    "SwapOverlapFiniteness",
    "OverlapFullRank",
    "OverlapBadSCCNormalForm",
    "OverlapBoundaryZipperDichotomy",
    "OverlapProductivity",
    "CoincidenceDensityOne",
    "AllStatesProductiveViaOverlaps",
    "DensityToPDSBridge",
    "PDSOverlapRoute",
    "AlignedOverlapsAreStrongCoincidence",
    "BoundaryCoincidenceCriterion",

    \* --- strongest Level-3 spectral route -------------------------------
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

      (* Level 2: G1b1 is repository-proved by the independent reconstruction.
         G1b2 is the open input for the stronger finite-BPA theorem. *)
      [] r = "G1b1BoundedDiscrepancy"    -> {}
      [] r = "G1b2RenewalFiniteness"     -> {"G1b1BoundedDiscrepancy"}
      [] r = "G1FromRenewal"             -> {"G1b1BoundedDiscrepancy", "G1b2RenewalFiniteness"}
      [] r = "G1"                        -> {"G1FromRenewal"}

      (* Overlap route: the seed-patch overlap graph is finite by bounded
         discrepancy.  OverlapProductivity remains the only open input of the
         shortest PDS route.  The two obstruction-normal-form nodes are proved
         constraints on a hypothetical failure; they do not discharge it. *)
      [] r = "SwapOverlapFiniteness"      -> {"G1b1BoundedDiscrepancy"}
      [] r = "OverlapFullRank"            -> {}
      [] r = "OverlapBadSCCNormalForm"    -> {"SwapOverlapFiniteness", "OverlapFullRank"}
      [] r = "OverlapBoundaryZipperDichotomy" -> {
          "OverlapBadSCCNormalForm",
          "AlignedOverlapsAreStrongCoincidence",
          "BoundaryCoincidenceCriterion"
      }
      [] r = "OverlapProductivity"        -> {}
      [] r = "CoincidenceDensityOne"      -> {"OverlapProductivity", "SwapOverlapFiniteness"}
      [] r = "AllStatesProductiveViaOverlaps" -> {"OverlapProductivity", "SwapOverlapFiniteness"}
      [] r = "DensityToPDSBridge"         -> {}
      [] r = "PDSOverlapRoute"            -> {"CoincidenceDensityOne", "DensityToPDSBridge"}
      [] r = "AlignedOverlapsAreStrongCoincidence" -> {}
      [] r = "BoundaryCoincidenceCriterion" -> {}

      (* Historical name retained for compatibility. The carrier span result
         is repository-proved; concentration and productivity remain open. *)
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

    "GaloisWedgePropagation",

    (* G1b1 and the conditional assembly are proved; G1b2 is absent. *)
    "G1b1BoundedDiscrepancy", "G1FromRenewal", "G1",

    (* Overlap route proved/supporting nodes. OverlapProductivity is absent. *)
    "SwapOverlapFiniteness", "OverlapFullRank", "OverlapBadSCCNormalForm",
    "OverlapBoundaryZipperDichotomy", "CoincidenceDensityOne",
    "AlignedOverlapsAreStrongCoincidence", "BoundaryCoincidenceCriterion",
    "AllStatesProductiveViaOverlaps", "DensityToPDSBridge", "PDSOverlapRoute",

    (* Boundary route conditional reductions remain proved. C4 itself is absent. *)
    "C3Local", "C2", "SCCProducer", "PDS",

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
