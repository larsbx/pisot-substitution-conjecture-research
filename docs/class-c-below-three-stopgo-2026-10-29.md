# Class C below slope three: stop/go (2026-10-29)

Dependency: #392 at 82dc6955faf68df5ee31292b9c2dd503b325a123, still open
and with queued hosted jobs at initial inspection. Use its exactly scoped
local certificates provisionally; do not infer hosted acceptance from them.
All earlier packets and implementations remain unchanged.

Target: lower the current slope-three frontier by exact lines n=3d+c,
and explore a sector between slopes 5/2 and 3 without assuming PIP, a common
label set, or successful closure. For integer A,B define

    u=2n-5d-A, v=3d-n-B,
    d=A+2B+u+2v, n=3A+5B+3u+5v.

This is an integral inverse with determinant -1, so the nonnegative orthant
represents exactly 2n>=5d+A and n<=3d-B, with no parity hypothesis.
Run lengths are affine. Reuse the existing symbolic cone engine and exact
PIP-domain lemma; fit no invariant or table from samples.

The primary-source check of class-c-lower-strip-stopgo-2026-10-29.md is
reused: Akiyama–Lee (2011), arXiv:1003.2898; Sellami (2015),
DOI 10.3906/mat-1407-3; Akiyama (2016), DOI 10.3934/dcds.2016027.
The same overlap-graph construction transfers, while complete legal-overlap,
unimodular and many-control-point hypotheses do not follow from swap-seed BH.
No new coincidence criterion or spectral consequence is proposed. Novelty
is restricted to certified parameter pieces and their reproducible cover.

Budget before new code: exact oracle profile at d=24,40,60 and
n=floor(5d/2)+j (j=0,4,8,12) or n=3d+c (c=-16,-8,-4,0,3,5);
four sector proposals (A,B)=(8,8),(16,8),(8,16),(16,16) per sign;
lines c=-8..3 plus and c=-8..5 minus, initially d>=32. If a sector has
changing labels, preserve the mismatch and redirect to line certificates
rather than calling count agreement a uniform proof. Smaller gaps below a
successful line floor can be decided exactly within the stated finite budget
6<=d<=31. Do not infer a conclusion from a cap or undecided sign.

Known controls: the minus 250-label table already fails at n=3d+5, and
#392 proves that intermediate clipping signs can vary even when label sets
agree. Also preserve the 282-count/different-label control. The lower edge
near n=2d may grow and remains distinct from these fixed-slope targets.

Decision: proceed with parameter-stratified cones and lines, independent exact
oracles, explicit failed proposals and exact source provenance. No all-strip,
PDS, G1 or PSC promotion is planned.

Profile-driven refinement before implementation: at d=24,40,60 the layers
near n=3d-8 and n=3d-4 differ from the interior 400/384 tables. A sector
with B=8 therefore cannot be certified by extrapolating one label set.
Retain all eight planned sector attempts, but expand the bridging line budget
to c=-15..3 plus and c=-15..5 minus (40 lines, d>=32). If a B=16 sector
certifies, these lines join it to #392's upper bound. The finite-end budget
is d=6..31 with n from ceil((5d+A)/2) through 3d+3/5, clipped to the proved
PIP domain. This is a finite, explicit enumeration, not a growing-state
uniform claim at the lower Pisot edge. If the sectors refuse, the line-only
result is retained with its own exact finite-end scope.

Hypothesis refinement after initial line refusals (before target-line code):
line n=3d+c intersects the proposed frontier 2n>=5d+A exactly when d>=A-2c.
Therefore the required line floor is max(32,A-2c), not blindly 32. At A=8
only c=-15,-14,-13 need raised floors 38,36,34. Add these six targeted
line replays (both signs) to the budget and retain all initial floor-32
attempts. A=16, if needed as the selected sector frontier, is a restriction
of an A=8 target-line certificate. If a targeted certificate also refuses,
record that fact before narrowing scope; no refusal is converted to BH failure.

Bounded exception split after c=-12 minus also refused at its required floor:
allow an explicit line floor 32..48, with every omitted target member below
that floor decided by the exact member kernel. Start c=-12 at d>=34 and
record d=32,33 individually. This is the same symbolic-tail/finite-end
construction used by T_C, without requiring one label set across the pieces.
No uncovered member is discarded. If later direct line attempts refuse,
apply this finite split within the same maximum floor 48 and preserve the
original error; the audit/oracle must check every exceptional integer.
