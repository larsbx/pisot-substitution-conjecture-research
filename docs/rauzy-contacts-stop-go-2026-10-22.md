# Exact Rauzy contacts from the box automaton: targeted literature stop/go check

**Status:** stop/go note under the review gate of `AGENTS.md`, dated 2026-10-22. It records the decision for:

- `kernel/psc/rauzy_contacts.mojo`;
- its driver `kernel/rauzy_contacts_census.mojo`;
- the oracle `oracles/python/rauzy_contacts.py`;
- the bundle `evidence/rauzy-contacts-2026-10-22/`.

It proves nothing, promotes no claim and changes no ledger entry. It follows `docs/rauzy-torus-stop-go-2026-10-21.md`, whose sampled lift profile could not resolve specimen #3742.

## Proposed experiment

Replace the sampled lift profile with exact per-specimen data the project already computes. For a unimodular PIP `σ`, with `P(w) = w − |w|₁ f` on `H = {Σx = 0}`, the record holds:

1. **The box verdict.** The Theorem Ω verdict of the box automaton (`psc.vertex_coincidence`), read from the same box the contacts come from.
2. **The contacts.** The set of `(i, j, w)`, `w ∈ Z³`, such that `R(i) + P(w) ∩ R(j) ≠ ∅`.
3. **The lattice neighbours.** The `(w₀, w₁)` of the contacts with `|w|₁ = 0`. These are the neighbours of `R` in its `Z²` tiling.

## Prior art and field terminology

1. Siegel and Thuswaldner, *Topological properties of Rauzy fractals*, Mém. SMF 118 (2009).
   - **Boundary graph and contact graph.** Nodes are pairs of subtiles with a translation in the self-replicating set.
   - **Criterion.** Through the set equation, an intersection is nonempty iff its node has an infinite walk. The criterion needs unimodularity.
   - **Tribonacci.** The lattice tiling has six neighbours.
2. Ito and Rao, *Atomic surfaces, tilings and coincidences I*, Israel J. Math. 153 (2006); Barge and Kwapisz, Amer. J. Math. 128 (2006). For unimodular irreducible Pisot `σ`, pure discrete spectrum ⇔ periodic tiling by `R` ⇔ covering degree 1.
3. Lee, Moody and Solomyak (2003), via this repository's `BoxAutomatonPDSCertificate` (proved). A productive box gives pure discrete spectrum, without using unimodularity.

## Hypotheses that transfer and hypotheses that do not

Transfer:

- **Overlap ↔ translate.** An oriented overlap `(i, j, t)` of `psc.overlap_seed_patch` has `t = ⟨l, w⟩` for a unique integral `w`. Its window `−l_j < t < l_i` is item 1's self-replicating window.
  - Read in `H`, it is the pair `R(i) + P(w)`, `R(j)`. The `+` sign was fixed against the exact sample of `rauzy-torus-2026-10-21`; the `−` sign fails on 14 of Tribonacci's and 53 of #3742's candidate pairs.
- **Contacts = descendants of cycles.**
  - A point of `R(i) + P(w) ∩ R(j)` lies in the image of a parent intersection. So the intersection is nonempty iff the overlap has an infinite ancestor chain.
  - In a finite potential-overlap graph that means reachable from a cycle.
  - Every cycle vertex lies in the box (`BoxCycleContainment`, proved) and the box is inflation-closed. So the box's cycle descendants, coincidences excluded, are the contacts.
  - This is item 1's criterion applied to this repository's graph. It is cited, not a ledger import.
- **Reversal.** Swapping top and bottom maps the potential-overlap graph to itself, so the contacts are closed under `(i, j, w) ↦ (j, i, −w)`. The kernel checks this and raises on a violation.

Do not transfer:

- **Covering degree 1** is item 2's conclusion applied to the proved box certificate. It has no ledger import here, so the record names that chain in a `consequence` string and never stores it as a fact.
- **Seed overlaps are not contacts.** This is the refuted stronger variant.
  - The first implementation assumed every overlap reachable from the swap seeds `ab | ba` occurs in a tiling, and raised when one was not a contact.
  - It raised on **1368 of the 2628** unimodular standing specimens.
  - The swap seeds are formal pairs. Specimen 1 (`1 2 5`) has no word `01`, and every stray state there descends from its `(0, 1)` seeds.
  - The seed graph is therefore not used. The refutation is pinned in `kernel/tests/test_rauzy_contacts.mojo`.
- **Non-unimodular `σ`** fall outside item 1's criterion and the torus picture (solenoid), so they are refused.

## Known negative controls and counterexamples

- **Tribonacci.** Item 1's six lattice neighbours `±(1,0), ±(0,1), ±(1,−1)` are reproduced exactly, from 28 contacts.
- **Smith.** 52 contacts and 8 lattice neighbours, closed under reversal.
- **A synthetic one-sided cycle.** The graph's only cycle is `(0, 1, t)` with no `(1, 0, −t)`; the kernel raises. A capped graph raises too.
- **Geometric control on #3742,** against the exact 65,536-point sample:
  - every contact comes within a sample gap of 0.016;
  - the 40 box vertices outside the cycle descendants nearest by centroid all stay at least 0.0845 away;
  - so contacts and non-contacts separate by a factor of five.
- **Independent oracle.** It rebuilds the potential graph on a different region, item 3's q-contraction region in `formal_overlap.py`, and agrees on every field of the named records.

## Decision

**Proceed.**

- Records have status `exact`. The box verdict is the repository's own exact verdict, and the contacts rest on item 1's criterion, which is cited.
- The lift profile of `rauzy-torus-2026-10-21` is kept as a sampled picture only. Its #3742 observation is explained, not overturned: #3742's tile has 20 lattice neighbours against Tribonacci's 6, so nearly every small cell touches a neighbour's boundary.
