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
