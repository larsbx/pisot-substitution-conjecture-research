------------------------------- MODULE Ledger -------------------------------
(***************************************************************************)
(* The concrete v15 / v34 ledger.  Labels follow                           *)
(* README_READ_FIRST_2026_09_08.md and PROOF_CERTIFICATE.md.               *)
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
    \* --- spectral module, PROOF_CERTIFICATE.md sections 3-10 ------------
    "PhiSemisimplicity",
    "ThetaIntertwining",
    "SeedCentralizer",
    "Target1",
    "DominantCubicCapture",
    "SpectralBlackBox",
    \* --- v33 / v34 route -------------------------------------------------
    "InterBlockCancellation",
    "DominantK2Source",
    "LoadBearingSCC",
    \* --- the open core ----------------------------------------------------
    "G1",
    "SCCProducer",
    "QuotientTransfer",
    "PDS",
    \* --- retracted ---------------------------------------------------------
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
      [] r = "G1"                       -> {}
      [] r = "SCCProducer"              -> {}
      [] r = "PDS"                      -> {"G1", "SCCProducer"}
      [] r = "V5Thm51"                  -> {}]

(* Standing proofs.  G1 and SCCProducer are absent: G1 is a hypothesis and
   SCCProducer is conj:producer, the main open target.  V5Thm51 is absent
   because its proof is withdrawn. *)
ProvedDef == {
    "DefectTheorem", "UniqueDecodability", "UDForPowers",
    "LocalWitnessInjectivity", "MassBalanceK2Obstruction", "AlgebraicEmbedding",
    "WedgeBound", "PhiSemisimplicity", "ThetaIntertwining", "SeedCentralizer",
    "Target1", "DominantCubicCapture", "SpectralBlackBox",
    "InterBlockCancellation", "DominantK2Source", "LoadBearingSCC",
    "QuotientTransfer", "PDS"
}

WithdrawnDef == {"V5Thm51"}

NoAssumptions == {}
G1AndProducer == {"G1", "SCCProducer"}
G1Only == {"G1"}
=============================================================================
