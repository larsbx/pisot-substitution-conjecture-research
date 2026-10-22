# Minus class-D recurrent diagnostics: targeted stop/go

Date: 2026-10-19. Decision recorded before the new diagnostic implementation.

## Proposed experiment

Repair PR #290's retired RC- test. Classify every recurrent vertex of the
complete, exact swap-seed graph at fixed integers a>=2,b>=1. Accept sealed
carrier vertices and U/Ubar/V/Vbar only after replaying their exits into that
carrier. A coincidence requires equal letters as well as zero displacement.
Keep distinct-letter zero-offset states in the classification. Separately,
refute specified complete affine cycles by conjoining all occurrence guards
over ONE shared u=a-2,v=b-1>=0. This is not a proof of CycleSum-.

## Primary sources inspected and transferable content

1. Akiyama and Lee, *Algorithm for determining pure pointedness of self-affine
   tilings*, Advances in Mathematics 226 (2011), 2855–2883,
   [full text](https://arxiv.org/html/1003.2898v1), especially Sections 2.4–2.5
   and 4. The affine child update and potential-overlap graph are established
   constructions. Their spectrum criterion requires the appropriate realized
   tiling/Meyer hypotheses and preserves edge multiplicities. A potential
   overlap can touch only at the boundary. We transfer the affine update and
   interior/coincidence distinctions, not a spectrum theorem for our seed graph.
2. Hune, Romijn, Stoelinga and Vaandrager, *Linear Parametric Model Checking of
   Timed Automata*, BRICS RS-01-5 (2001),
   [publisher record and paper](https://tidsskrift.dk/brics/article/view/20459).
   Symbolic parameter constraints are prior art. The paper's decidable L/U
   subclass does not establish termination for this unbounded overlap-state
   problem. Accumulating guards is an elementary specialization, not a new
   general parameter-synthesis theorem.
3. Minervino and Thuswaldner, *The geometry of non-unit Pisot substitutions*,
   Annales de l'Institut Fourier 64 (2014), 1373–1417,
   [publisher record](https://aif.centre-mersenne.org/articles/10.5802/aif.2884/).
   Non-unit representation spaces include finite-place factors. No Euclidean
   stable-lattice shortcut or unimodular substitution theorem transfers to
   this determinant-two family. This work supplies no CycleSum- bound.

Reuse the more detailed local literature audits in
`p1-overlap-affine-pump-literature-gate-2026-09-15.md` and
`seed-patch-to-literature-overlap-audit-2026-09-13.md`; neither identifies the
seed graph with the full tiling overlap graph without further hypotheses.

## Negative controls and scope boundary

RC- is false: U/Ubar already cycle for b<=a. Their productive exits make them
controls against carrier-only rejection. Distinct-letter zero displacement is
not a terminal coincidence. A cycle whose edges require v=2u+7 and v<=u is
incompatible over u,v>=0 even though each edge can be feasible separately.
Real feasibility alone need not imply integer feasibility, interior geometry,
or seed reachability. A bounded state/cycle search cannot cover unbounded sums.

## Decision

Proceed with the narrowed exact diagnostic and explicit whole-cycle
infeasibility certificates. Preserve ordered occurrences in replay reports.
Fail closed on caps, arithmetic rejection, unexplained recurrent labels, or
failed exceptional exits. Do not delete edges on failure to find a Farkas
certificate. Leave CycleSum-, universal #139/#84, and PSC open. Novelty is
restricted to this family's classification, replay data and checked reduction.

## Continuation decision: one unbounded six-edge family

The three primary sources above were revisited before implementing this
extension. Narrow the target to the documented six-edge segment itinerary,
with cyclic sums `(-k,k-1,-k,k-1,-k,k)` for an arbitrary integer `k>=2`.
Use the x/c predecessor identities to reconstruct its offsets symbolically,
then derive the occurrence guards as exact polynomials in `k`, affine in the
ONE shared `u,v`. Check whether the same two unit multipliers cancel `k`
and `v` identically. This is specialization of affine guard conjunction and
a constant Farkas certificate, not a parameter-synthesis or completeness
theorem. The non-unit and seed-realization limitations remain unchanged.

**Proceed, narrowly:** a polynomial identity can exclude this whole unbounded
family without a finite k cap. It does not show that every higher-sum cycle
has this itinerary or sum pattern. Retain the k=2 individually feasible-edge
control, the feasible U/Ubar control, and closing-edge mutation refusal.
No cycle enumeration, universal invariant test, or claim promotion is licensed
by this family calculation alone.

## Next decision: scalar reconstruction and a stronger-claim control

Revisit the same three primary sources for the distinction between formal
occurrence cycles, interior geometry and seed reachability. The next proposed
step eliminates x/c coordinates from a cyclic itinerary using the last two
scalar sums and endpoint-prefix differences. This is an elementary consequence
of the affine child update, not a new overlap-coincidence theorem.

Before seeking a universal shared-guard refutation, test its necessary stronger
claim: that all genuine formal cycles have |s|<=1, even without seed
reachability. The two-cycle itinerary LAST/RUN then RUN/LAST suggests scaled
states U_k=(y,c,-2k,4k,-3k) and their mirrors. Its guards allow
k(b+1)<=a+1 with ONE common a,b. On the ray a=2k-1,b=1, k>=2, check the
occurrence identities symbolically and both interior margins exactly. If this
succeeds, stop trying to exclude all higher-sum formal cycles by shared guards
alone; redirect to the seed-reachability premise. Keep the canonical seed
diagnostic fail-closed on any observed seed-reachable higher-sum label.

**Proceed with this negative control and scalar derivation only.** Distinguish
an unbounded formal-cycle theorem from finite seed-graph membership checks.
Neither the earlier six-edge exclusion nor a feasible formal cycle decides
CycleSum- without its seed qualifier. Non-unit representation hypotheses remain
unchanged; no published theorem supplies that missing qualifier here.

## Seed-closure decision (2026-10-20 UTC)

Revisited the three primary sources above before this experiment. Akiyama–Lee's
inflation closure motivates checking every interior occurrence child; selected
paths into a ranked carrier do not prove forward invariance. The non-unit
representation and realization hypotheses remain untransferred. Parametric
guards must refer to one fixed substitution throughout a seed path.

**Proceed narrowly:** inspect complete swap-seed graphs, then test whether the
sealed carrier augmented by seed/terminal labels is a conditional forward
upper cover for all a>=2,b>=1. A cover label need not be real at every parameter;
only real sources and their real children impose closure obligations. First
try the existing exact normalized root box, preserving any relaxed-geometry
escape and any actual parameter witness. Do not assume that a finite grid or
selected ranked exits imply closure. The feasible U_k high-sum cycles are the
negative control: a seed invariant must exclude them for a reason beyond
shared occurrence guards and interiority. A failed cover is a research result,
not grounds for asserting CycleSum- or deleting an edge. Any successful proof
must cover initial seeds and all child segments without parameter switching.

**Outcome:** the narrowed route succeeds using two correlated Perron bounds.
The result is a seed-specific forward carrier, not unrestricted formal-cycle
inclusion or a new general tiling-spectrum theorem. The exact geometry and
all-child induction are in section 14 of the research note. The original
shared-guard and high-sum formal controls remain valid; no realization or
unimodularity hypothesis is waived. The scoped CycleSum claim now follows
from this separate seed certificate, with pinned CI/human validation pending.
