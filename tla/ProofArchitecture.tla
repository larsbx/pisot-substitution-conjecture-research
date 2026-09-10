--------------------------- MODULE ProofArchitecture ---------------------------
(***************************************************************************)
(* Generic dependency state machine for the PSC research program.           *)
(*                                                                         *)
(* A result is established only by explicit assumption or by discharging a  *)
(* standing proved theorem after all of its prerequisites are established.   *)
(* Withdrawn results can never be discharged.                               *)
(*                                                                         *)
(* Requires encodes one-way proof sufficiency/dependency. It must not be     *)
(* read as a converse mathematical implication.                              *)
(*                                                                         *)
(* All currently ready results are discharged in one batch. This computes   *)
(* the same least dependency closure as arbitrary one-at-a-time discharge,   *)
(* but avoids exploring factorially many equivalent proof orders as the      *)
(* ledger grows. Each non-stuttering step advances one dependency layer.     *)
(***************************************************************************)
EXTENDS FiniteSets

CONSTANTS
    Results,
    Requires,
    Proved,
    Withdrawn,
    Assumed

ASSUME
    /\ Proved \subseteq Results
    /\ Withdrawn \subseteq Results
    /\ Assumed \subseteq Results
    /\ Proved \cap Withdrawn = {}
    /\ Requires \in [Results -> SUBSET Results]

VARIABLE established

vars == <<established>>

Init == established = Assumed

Ready == {
    r \in (Proved \ established) : Requires[r] \subseteq established
}

Next ==
    /\ Ready # {}
    /\ established' = established \cup Ready

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Soundness invariants *)

TypeOK == established \subseteq Results

NothingUnjustified == established \subseteq (Proved \cup Assumed)

NoWithdrawnDependency ==
    /\ established \cap Withdrawn = {}
    /\ \A r \in established : Requires[r] \cap Withdrawn = {}

-----------------------------------------------------------------------------
(* Configuration-specific observables. A model may assert one negatively so  *)
(* that a TLC violation trace demonstrates the positive derivation.          *)

MainResultIsConditional == "PDS" \notin established

SpectralBlackBoxNotYetDerived == "SpectralBlackBox" \notin established

LoadBearingSCCIsConditional == "LoadBearingSCC" \notin established

(* The current C4 route is not unconditional: without assumptions C4 is not  *)
(* established and therefore SCCProducer must remain unreachable.            *)
SCCProducerIsConditional == "SCCProducer" \notin established

(* The literature theorem and the repo seed-union lemma are recorded, but    *)
(* the final seedwise PDS=>repo-G1 implication is deliberately still open.   *)
RepoG1BridgeRemainsOpen == "PDSImpliesRepoG1" \notin established

=============================================================================
