# Realization-preserving packet square: literature stop/go gate — 2026-11-10

**Status:** stop/go note (AGENTS.md "Targeted literature stop/go check") for the
second item of the 2026-11-09 priority addendum of `README.llm.txt` ("P0
OCCURRENCE REFINEMENT") and item (2) of the immediate sequence in
[research-roadmap-2026-09-21.md](research-roadmap-2026-09-21.md) ("realization-
preserving packet square"). It moves no governed claim status and adds no ledger
claim.

## 0. Decision

**Proceed, narrowed.** A commuting square between a concrete transition system
and an abstract one, split into a forward condition, a backward condition and
path lifting, is textbook simulation theory; which path properties each condition
transfers is a textbook theorem. The address-carrying pair graph is the
prefix–suffix automaton of Canterini–Siegel read on two tracks, with the
difference of prefix abelianisations as the carried vector: that shape is in
print as the boundary graph of Siegel–Thuswaldner (unit Pisot) and as the
potential-overlap graph of Akiyama–Lee. Nothing in the logic or the construction
is new. The work is restricted to

1. a typed Lean interface, graph logic only, with completeness, soundness (from
   some source and from every source), target preservation and target reflection
   as separate hypotheses, the transfer of each reading of
   [Psc.QuantifierInterface](quantifier-transfer-audit-2026-11-09.md) under exactly
   the hypotheses it needs, and a countermodel for each dropped hypothesis;
   `PscVerif.QuotientDistance.Refinement` is its finite functional instance and is
   reused, not duplicated;
2. a literal finite replay on fixed specimens that checks each certified packet
   transition against the literal balanced-pair factorisation and checks that
   every child occurrence of every listed state is present, with the existing
   controls rejected at the literal layer;
3. infinite path lifting stated only as a consequence of soundness at every
   source, or of finite lifts under finite branching, never from a bounded or
   existential certificate.

No census, no corpus computation, no statement about finiteness of any packet
graph, no realisation of a quotient cycle as a literal cycle, and no inference of
ancestry from recognizability is licensed by this note.

Item 1 is `proof/PscVerif/PscVerif/GraphRefinement.lean` (this revision). Items 2
and 3 wait for a design pass over the Mojo packet code
(`kernel/psc/target_packets.mojo`).

## 1. The proposed claim

Child graphs `G` (literal occurrences) on `X` and `P` (packets) on `Y`, and a
projection `π : X → Y`:

| Name | Statement | Textbook name |
| --- | --- | --- |
| `Complete` | `x → x′` in `G` gives `π x → π x′` in `P` | forward condition: `P` simulates `G` |
| `SoundSome` | every `P`-edge is the image of some `G`-edge | (none; strictly weaker) |
| `SoundEvery` | `π x → y′` in `P` gives `x → x′` in `G` with `π x′ = y′` | backward condition: `G` simulates `P` |
| `TargetDown`, `TargetUp` | targets are preserved, reflected | label condition |
| `LiftsPaths x` | every infinite `P`-path from `π x` is the image of a `G`-path from `x` | path lifting |

Transfers, with the readings (E) some path reaches a target, (AE) every reachable
state does, (A) every infinite path meets one:

| Hypotheses | Transfer |
| --- | --- |
| `Complete` + `TargetDown` | (E) at `x` ⇒ (E) at `π x` |
| `SoundEvery` + `TargetUp` | (E) at `π x` ⇒ (E) at `x` |
| `Complete` + `TargetUp` | (A) at `π x` ⇒ (A) at `x` |
| `SoundEvery` | `LiftsPaths x` (dependent choice; no branching hypothesis) |
| `LiftsPaths x` + `TargetDown` | (A) at `x` ⇒ (A) at `π x` |
| `Complete` + `SoundEvery` + `TargetDown` | (AE) at `x` ⇒ (AE) at `π x` |
| `Complete` + `SoundEvery` + `TargetUp` | (AE) at `π x` ⇒ (AE) at `x` |
| finite lifts of every prefix + finitely many children at each state | `LiftsPaths x` (König) |

"Lies on a cycle" does not transfer from `π x` to `x`, even with all hypotheses
and a finite actual graph; only "reaches a cycle" does.

## 2. Prior art

The sources were fetched on 2026-11-10 by a reader agent of this pass, and the
quotations below were then checked by the lead against the saved text layers;
sha256 prefixes identify the copies.

1. **V. Canterini, A. Siegel, *Automate des préfixes-suffixes associé à une
   substitution primitive*, J. Théor. Nombres Bordeaux 13 (2001), 353–369**
   (Numdam scan, `708c3e1a74ef25fc`; OCR text layer). Définition 3.1: an arrow from
   `a` to `b` labelled `e = (p, a, s)` "si σ(b) = pas". Proposition 6.1: for
   `n < |σ^k(a)|` there is "un unique chemin de longueur k" of the automaton
   arriving at `a` that encodes the position. Forward uniqueness of the address of
   a position inside `σ^k(a)` is therefore elementary; an occurrence address is a
   path in this automaton.
2. **A. Siegel, J. M. Thuswaldner, *Topological properties of Rauzy fractals*,
   Mém. Soc. Math. France 118 (2009)** (`262111fe20b41fb8`). Definition 2.5
   (prefix-suffix graph), Definition 5.4 (boundary graph: nodes `[i, γ, j]`, edges
   carrying two prefix–suffix labels and updating `γ` by the difference of prefix
   abelianisations; "the largest graph" with the stated conditions), Proposition
   5.5 ("The boundary graph associated with a finite subset S of D is well defined
   and finite"), Theorem 5.6 (the intersection of `T(i)` and `T(j) + γ` is
   nonempty iff `[i, γ, j]` is a node). The setting is unit Pisot substitutions.
3. **B. F. Martensen, *A generalized balanced pair algorithm*,
   arXiv:math/0309194** (`456d6ef4f6de0b9d`). §3.1, `I_n(w)`; the proof of
   Theorem 3.10 uses the substitution `φ̂` on irreducible balanced pairs, whose
   graph has an edge into each letter of `φ̂(β)` "with multiplicities". The
   literature's child graph keeps multiplicities but not ordinals or addresses.
4. **S. Akiyama, J.-Y. Lee, arXiv:1003.2898** (`5b34298e8d86a5d4`). Lemma 2.6:
   every overlap is a potential overlap (the forward condition). §4: "Keeping the
   multiplicity in the graph is essential to distinguish real overlaps from
   potential overlaps that are not", and boundary-touching potential overlaps give
   infinite walks on the graph. Abstract infinite walks need not be realised; the
   criterion compensates by a spectral-radius comparison, not by lifting.
5. **V. Berthé, W. Steiner, J. M. Thuswaldner, R. Yassawi, *Recognizability for
   sequences of morphisms*, arXiv:1705.00167** (`02580261ca32dc66`). Theorem 3.1:
   a morphism with `rk(M_σ) = |A|`, or on two letters, or left or right
   permutative, "is fully recognizable for aperiodic points"; the introduction
   draws the consequence for irreducible Pisot substitutions. Recognizability is
   uniqueness of the backward step for two-sided aperiodic points.
6. **J.-P. Katoen, *Model Checking*, lecture 24 "Simulation preorder", RWTH
   Aachen, 2007** (`82eb59045cf7f310`; slides for Baier–Katoen, *Principles of
   Model Checking*, ch. 7, whose theorem numbers were not checked). "Let TS be a
   finite transition system (without terminal states)": simulation order is
   characterised by preservation of ∀CTL* formulas in one direction and of ∃CTL*
   formulas in the other; the overview table gives CTL* only for bisimulation.

Not read, and carrying no weight: Sirvent–Solomyak (2002), Dumont–Thomas (1989),
Mossé (1992, 1996), Milner (1989), Park (1981), Clarke–Grumberg–Jha–Lu–Veith on
counterexample-guided abstraction refinement (2003), and Kőnig (1927); the König
step is proved directly in Lean here.

## 3. Hypotheses that transfer, and those that do not

| Fact | Transfers to the standing regime? |
| --- | --- |
| Forward uniqueness of an address in `σ^k(a)` (source 1) | Yes; it uses only that `σ` is nonerasing. |
| Recognizability (source 5) | For two-sided aperiodic points only. A balanced pair is a finite word with a boundary, where one-sided uniqueness can fail, and recognizability does not make the cuts of two tracks agree (recorded in `docs/branch-b-prefix-suffix-literature-gate-2026-10-19.md`). |
| Boundary graph and its finiteness (source 2) | As a shape, yes. As a theorem, no: it is stated for unit Pisot substitutions and subtile intersections, and the standing class is not unimodular. |
| Finiteness of the pair graph | Not supplied by any source; in the repository it is G1-type input. |
| Simulation ⇒ ∀CTL* / ∃CTL* (source 6) | Stated for a finite system without terminal states. Neither holds here (coincidence blocks are terminal, `Psc.Descendants.ChildNC`; a retained packet graph can have dead ends). Nothing is imported: the transfers of §1 are proved directly. (AE), the reading of the spectral criterion, mixes both quantifiers and needs both directions. |
| Infinite path lifting | From soundness at every source: yes. From prefix lifts: only with finite branching; a packet has infinitely many occurrences in the fixed point, so a lifting tree rooted at "some occurrence" branches infinitely at the root. |

No unimodularity is used.

## 4. Known negative controls

Already formal in the repository:
`PscVerif.QuotientDistance.one_sided_cannot_lift` and `one_sided_original_trapped`
(projection and matching terminals without lifting from every source);
`PscVerif.SelectedRank.control_carrier_not_closed`;
`proof/psc_routes/R1OrderedAncestry.lean` `bounded_candidate_absent` (an arithmetic
cycle not realised in a bounded scan of one seed);
`kernel/tests/test_ordered_occurrence_graph.mojo` (two occurrences with different
ordinals are not merged).

Recorded decisions on adjacent constructions:
`docs/finite-quotient-lean-stopgo-2026-11-02.md` (lifting from every source
required; no novelty claimed), `docs/selected-rank-lean-stopgo-2026-10-31.md` (the
implementation-refinement bridge is a separate obligation),
`docs/target-aware-bpa-literature-gate-2026-10-02.md` (only the realisable
occurrence graph; split descendants and exhausted budgets reported),
`docs/boxwalk-reachability-realizability-audit-2026-10-15.md` (projected vector
edges from different occurrences can splice unrealisable paths), and
`docs/automatic-sequence-route-literature-gate-2026-09-17.md` (Dumont–Thomas).

New in this revision, `Psc.GraphRefinement`: `dropped`, `undrawn` (completeness
cannot be dropped), `overdrawn`, `overdrawnFork` (soundness cannot be dropped),
`broken` (soundness from some source is not enough), `unroll`, `tail` (a quotient
cycle need not be realised by a cycle), `fan` (prefix lifts without an infinite
lift).

## 5. Non-claims

This note and `Psc.GraphRefinement` prove nothing about any packet graph, any
balanced-pair automaton or any substitution. In particular they do not show that
the Mojo packet graph is complete or sound with respect to literal occurrences,
that any packet cycle is realised, or that any graph is finite. They do not close
or advance C4, G1, #84, #138, #139 or PSC.
