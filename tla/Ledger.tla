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
(* C4 -> C3Local -> C2 -> SCCProducer is encoded only as a sufficiency      *)
(* route. No converse implication is asserted.                              *)
(***************************************************************************)
EXTENDS ProofArchitecture

ResultSet == {
    \* --- symbolic side, v15 theorem-grade -------------------------------
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
    "QuotientTransfer",

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
      [] r = "QuotientTransfer"         -> {"SpectralBlackBox"}

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

      (* C4 is open. If granted, the proved reduction chain discharges C1. *)
      [] r = "C4"                       -> {}
      [] r = "C3Local"                  -> {"C4", "C3Locality"}
      [] r = "C2"                       -> {"C3Local"}
      [] r = "G1"                       -> {}
      [] r = "SCCProducer"              -> {"G1", "SinkSCCReduction", "C2"}
      [] r = "PDS"                      -> {"G1", "SCCProducer"}

      (* Literature theorem and repository-side seed-union lemma are proved
         separately. The final PDS=>repo-G1 bridge remains open pending the
         seedwise termination/reachability implication. *)
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
    "QuotientTransfer",

    "SinkSCCReduction", "C3Locality", "EndpointCore", "GlobalEndpointSync",
    "SignatureReduction", "ParikhIntertwiner", "OrientationMonodromy",
    "OrientationSpectrum", "DefectIntertwiner", "W3LowGrowth",
    "Degree4Floor", "Mod3Sieve", "ParitySieve", "MidArea",
    "MeanAreaLift", "LatticeLift",

    (* These are proved conditional reductions. C4 itself is deliberately
       absent, so C3Local/C2/SCCProducer remain unreachable unless C4 is
       explicitly assumed. *)
    "C3Local", "C2", "SCCProducer", "PDS",

    "StandardBPAEquivalence", "RepoSeedUnionBridge"
}

WithdrawnDef == {"V5Thm51"}

NoAssumptions == {}
G1AndProducer == {"G1", "SCCProducer"}
G1Only == {"G1"}
G1AndC4 == {"G1", "C4"}
=============================================================================
