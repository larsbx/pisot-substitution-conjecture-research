# Class C slope-three continuation: stop/go (2026-10-29)

**Historical experiment, superseded 2026-11-01.** PR #392 is closed; this
record is retained for provenance and replay. The accepted mainline T_C and
T_C2 union covers d>=6, n>=3d and replaces every use of this weaker upper
bound in #394. The original derivation and budgets below describe that
historical experiment. Its workflow is archived, not an active acceptance
gate. See [the reconciliation](class-c-below-three-integration-2026-11-01.md).

Dependency: merged #390, main 625154ed470df4eef89577e421026f0c808287fd at session start (full SHA is in
the provenance packet). Its hosted certificate jobs remain queued; merge
status is not a successful replay receipt. Reuse its local certificates at
their recorded scope, keeping hosted acceptance and human-review debts explicit.

Target: close the upper gap between the middle cone and T_C by certifying
3d+a<=n<=4d-b with smaller a,b, adjoining finitely many n-4d diagonals,
and deciding the finite small-d end pieces. A successful cover would give
BH for every d>=6 above one slope-three bound, without assuming a common
label set across pieces. No spectral consequence is proposed.

The primary-source check in class-c-lower-strip-stopgo-2026-10-29.md is
reused: Akiyama–Lee (2011), arXiv:1003.2898; Sellami (2015),
DOI 10.3906/mat-1407-3; Akiyama (2016), DOI 10.3934/dcds.2016027.
This is the same parametric overlap construction and the same hypotheses,
not a new invariant or coincidence criterion. The first source's complete
legal-overlap hypotheses and the other sources' unimodular/many-control-point
hypotheses still do not transfer from a canonical swap-seed BH certificate.
Novelty is restricted to the covered parameter region and reproducible proof.

Use the unchanged engine and exact PIP-domain lemma. Explore a finite stated
budget of corner constants and diagonals using the existing exact oracle
and Mojo driver. Samples select proposals only; only a successful symbolic
closure and hitting test establishes a quantified region. Preserve refused
stronger corners and their exact messages. The adjacent 198/216 controls and
the 2,432-label gap-6 start forbid assuming the frozen-tail labels.

Decision: proceed with narrowed slope-three and diagonal cover targets.
Do not claim minimal constants or all-strip BH from a finite search. Keep
caps, small-gap coverage, exact parameter inverses and independent oracle
comparisons visible. Source kernels and old evidence packets remain unchanged.


The exploratory budget is eight corner pairs: plus (a,b)=(4,10),(8,10),
(4,16),(8,16); minus (6,4),(8,4),(6,16),(8,16). At most 26 bridging
diagonals c=-15..-5 plus and c=-15..-1 minus are tried at d>=24. If no new
corner certifies, the recorded a=b=16 cone is the fallback; that still closes
the upper gap after bridging. Finite end records use a=4 plus and a=6 minus,
d=6..23, regardless of the ultimately selected uniform intercept. This is
414 explicitly bounded members, potentially stronger at small gaps than the
uniform conclusion. No further corners are included in this run’s stated budget.

Refined partition after exact refusal (before new line code): the plus
(a,b)=(4,16) cone certifies, whereas minus (6,16) refuses on a comparison
whose beta-sign changes between u=0 and u=20. Redirect that lower edge to
separate n=3d+6 and n=3d+7 lines, and use (8,16) as the minus interior
candidate. These are affine one-parameter substitutions on the same engine,
with the same PIP, closure, hitting and constant-offset checks. Two extra
lines at d>=24 are added to the stated budget; no new sign engine is proposed.
The sampled minus n=3d+5 control remains outside this proposed cover.
