--------------------------- MODULE ProofArchitecture ---------------------------
(***************************************************************************)
(* The dependency structure of the PSC program as a state machine.          *)
(*                                                                         *)
(* Motivation.  Between June and September 2026 the project's certificate   *)
(* documents carried an "unconditional" claim for a result that in fact     *)
(* rested on PSC_PROOF_v5 Theorem 5.1, whose proof had been withdrawn       *)
(* (the predecessor-contraction inequality beta * L(s') <= L(s) + D is      *)
(* false; worst observed ratio 8.0, excess unbounded).  A prose ledger did  *)
(* not catch it.                                                           *)
(*                                                                         *)
(* This module makes the ledger executable.  A result may be established    *)
(* only when every prerequisite is already established, and a withdrawn     *)
(* result can never be established at all.  Model checking then decides,    *)
(* mechanically, which claims are reachable from which hypotheses.          *)
(***************************************************************************)
EXTENDS FiniteSets

CONSTANTS
    Results,    \* every named result in the program
    Requires,   \* Requires[r] is the set of prerequisites of r
    Proved,     \* results with a standing proof, given their prerequisites
    Withdrawn,  \* results whose proof has been withdrawn
    Assumed     \* hypotheses granted in this model configuration

ASSUME
    /\ Proved \subseteq Results
    /\ Withdrawn \subseteq Results
    /\ Assumed \subseteq Results
    /\ Proved \cap Withdrawn = {}
    /\ Requires \in [Results -> SUBSET Results]

VARIABLE established

vars == <<established>>

Init == established = Assumed

Discharge(r) ==
    /\ r \notin established
    /\ r \in Proved
    /\ Requires[r] \subseteq established
    /\ established' = established \cup {r}

Next == \E r \in Results : Discharge(r)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Soundness invariants: true of every configuration *)

TypeOK == established \subseteq Results

(* Nothing is ever established except by proof or by explicit assumption. *)
NothingUnjustified == established \subseteq (Proved \cup Assumed)

(* No withdrawn result is ever used, directly or as a prerequisite. *)
NoWithdrawnDependency ==
    /\ established \cap Withdrawn = {}
    /\ \A r \in established : Requires[r] \cap Withdrawn = {}

-----------------------------------------------------------------------------
(* Configuration-specific claims.  Each is stated as an invariant so that a *)
(* TLC violation exhibits the derivation as a counterexample trace.         *)

(* Holds when Assumed = {}: the boxed main result is NOT unconditional. *)
MainResultIsConditional == "PDS" \notin established

(* Holds when Assumed = {}: the spectral module of PROOF_CERTIFICATE.md
   section 14 is finite algebra and needs no hypothesis.  Stated negatively so
   that a violation trace exhibits its derivation. *)
SpectralBlackBoxNotYetDerived == "SpectralBlackBox" \notin established

(* Holds when Assumed = {}: the alphabet-3 spectral lower bound of v34 is
   conditional on G1, so it must not be reachable without it. *)
LoadBearingSCCIsConditional == "LoadBearingSCC" \notin established

=============================================================================
