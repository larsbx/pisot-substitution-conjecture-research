# Occurrence path replay: stop/go gate (2026-10-16)

Decision before implementation: **proceed with a finite witness checker**.
This is a certificate-semantics improvement, not a new coincidence criterion
or a universal productivity experiment. General PSC and G1 remain open.

## Sources and transfer boundary

1. Sirvent–Solomyak, *Pure discrete spectrum for one-dimensional substitution
   systems of Pisot type* (2002), DOI
   [10.4153/CMB-2002-062-3](https://doi.org/10.4153/CMB-2002-062-3).
   The publisher abstract was inspected: balanced-pair and overlap algorithms
   and their relationship are established prior art. This check does not import
   a new equivalence from an unread proof. The repository's existing detailed
   treatment is `bpa-termination-by-overlap-depth-2026-10-02.md`.
2. Akiyama–Lee, *Algorithm for determining pure pointedness of self-affine
   tilings*, [arXiv:1003.2898](https://arxiv.org/pdf/1003.2898),
   introduction and §§2.3–2.5, Definition 2.4 and Theorem 2.5 inspected.
   Coincidence requires the same position **and tile type**; inflation chooses
   actual descendants. Their spectral criterion concerns every overlap in a
   self-affine tiling with the Meyer hypothesis. Our finite swap-patch witness
   supplies neither the complete tiling dictionary nor this universal premise.
   Their construction includes non-unit cases; unit-only restrictions must not
   be imposed on local overlap replay.
3. Mercat–Akiyama, *Yet another characterization of the Pisot substitution
   conjecture*, [arXiv:1810.03500v1](https://arxiv.org/abs/1810.03500v1).
   The author abstract's irreducible **unit** Pisot restriction was inspected;
   the existing `mercat-akiyama-interior-language-gate-2026-10-12.md` records
   the earlier full-text review. No interior-language/PDS equivalence is
   transferred to the non-unit positive control here.

## Proposed scope and controls

Reuse exact cubic overlap geometry and labelled child positions. Anchor each
certificate to a specified swap-seed occurrence and substitution, and replay
each next source against the preceding computed child. For symbolic balanced
pairs, retain the complete ordered pair and paired image read heads; require
a nonterminal equal-letter cut with zero prefix-Parikh difference. An
imbalance-only path is an overapproximation, never an accepting certificate.

Controls: `12|21` terminal zero; incompatible balanced contexts spliced under
the same substitution; the actual `(k,h)=(3,2)` recurrent overlap with a distinct
two-step productive exit; malformed addresses, false half-coincidence targets,
and exhausted budgets. A cycle is not a child-closed nonproductive component.
There is no proposed SCC exclusion or general termination assertion.

The soundness argument will be induction on explicit occurrences, independent
of graph-search completion. Search exhaustion must not promote an absence or
universal claim. Arithmetic refusal must propagate, never become a success.

## Concurrent main correction incorporated

PR #271 (`ca646f28`) merged while the implementation was being tested. Its
October 16 prior-art correction identifies the **entire ternary control family**
as already PDS by the existing mirror-Barge imports. This reinforces the
original narrow go decision: keep it as a loop/exit certificate calibration,
never as new family-level PSC coverage. The merged source correction and its
new Barge witness regression are preserved in this branch.

The concurrently added attainment register prompted an explicit interface
cross-check with `psc.target_packets`: it already replays occurrence-sensitive
paths in a **complete BPA graph**. Retain that machinery and add only the
graph-independent witness boundary and the overlap-labelled search. An
integration regression exports its immediate successful factors into the new
checker. Its optional synchronization target is intentionally not identified
with immediate equality. This narrows reuse/novelty claims, not mathematical
coverage.
