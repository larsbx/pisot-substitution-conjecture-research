# Formal productivity = aligned strong coincidence + boundary hitting — 2026-10-04

**Status:** research note, not yet reviewed. Proposition FP is stated and
proved below from elementary facts; Corollary FP′ additionally rests on the
unreviewed Proposition V and Theorem S of
`p1b-vertex-coincidence-box-2026-10-02.md` and on the imported
Barge–Štimac–Williams density theorem behind manuscript Theorem 5.38. No
ledger node, open problem, or PSC status changes. Step 3 of the
realization programme following `formal-overlap-carriers-2026-10-04.md`.

## 1. Statement

Fix a primitive irreducible Pisot `sigma` on three letters. A *potential
overlap* is a genuine overlap `(i, j, t)`, `t = <ell, w>`, `w in Z^3`, with
children as in the manuscript; for a state `x` let `D(x)` be its first
coincidence depth and `L(x)` its first offset-zero depth (the state itself
included; `-1`/infinite if none).

- **FP(`sigma`)** — formal productivity: every potential overlap is
  productive.
- **SC_all(`sigma`)** — the six aligned pairs `(i, j, 0)`, `i != j`, are
  productive (all-pairs left strong coincidence).
- **BH(`sigma`)** — boundary hitting: every overlap lying on a cycle has an
  offset-zero descendant.
- **`S(sigma)`** `= max_{i != j} D(i, j, 0)` when SC_all holds.

**Proposition FP.**

1. If SC_all(`sigma`) holds, then `D(x) <= L(x) + S(sigma)` for every
   potential overlap `x` with `L(x)` finite.
2. FP(`sigma`) ⟺ SC_all(`sigma`) ∧ BH(`sigma`).

## 2. Proof

The offset-zero states are the `(i, j, 0)`: those with `i = j` are the
coincidences and the other six are the aligned pairs. `t = 0` is a genuine
overlap for every `i, j`, so all six are potential overlaps.

1. Let `y` be an offset-zero descendant of `x` at depth `L(x)`. Either `y` is a
   coincidence, and `D(x) <= L(x)`, or `y` is an aligned pair, and
   `D(x) <= L(x) + D(y) <= L(x) + S(sigma)`.
2. (⇒) The six aligned pairs are potential overlaps, so FP gives SC_all. A
   coincidence is offset zero, so a productive overlap has an offset-zero
   descendant; FP gives BH.

   (⇐) Suppose `x` is a nonproductive potential overlap. A noncoincidence
   overlap has at least one child, and every child of a nonproductive state is
   nonproductive (a productive child would make the parent productive). By item 5 of §2 of
   `formal-overlap-carriers-2026-10-04.md`, the resulting infinite
   nonproductive path repeats a state, giving a nonproductive cycle; let `v`
   be on it. BH gives an offset-zero descendant `y` of `v`. If `y` is a
   coincidence, `v` is productive; otherwise `y` is an aligned pair,
   productive by SC_all, and again `v` is productive. Contradiction.

`square`

## 3. Consequences

**Corollary FP′** (dependencies as listed in the status line). For PIP
`sigma`:

```text
FP  <=>  PDS and SC_all.
```

- FP ⇒ SC_all by Proposition FP.
- FP ⇒ PDS: every overlap reachable from a swap seed is a potential overlap
  (seed shifts are differences of tile lengths, and children keep `t` in
  `<ell, Z^3>`), so FP gives `OP_all` and `OP_seed`; manuscript Theorem 5.38
  (with the imported Barge–Štimac–Williams theorem) gives PDS.
- PDS ∧ SC_all ⇒ FP: Theorem S gives PPVC from PDS, Proposition V (1)–(2)
  turns PPVC into BH (its box contains every cycle vertex, and its
  every-vertex condition is equivalent to the every-cycle-vertex one by its
  step 3), and Proposition FP closes.

So the realization-free statement costs, beyond pure discrete spectrum,
exactly all-pairs aligned strong coincidence: three letter pairs, each a
single state.

**For the two routes of `p1-two-route-map-2026-10-01.md`.**

- Route A, in formal form, is SC_all: no SCC structure remains once the
  realization requirement is dropped. The fixed-edge / alternating-E normal
  form concerns how a pair can fail SC_all.
- Route B, in formal form, is BH, which Proposition V identifies with PPVC.
  Proposition FP says route B never has to deliver more than an offset-zero
  hit: the remainder is bounded by `S(sigma)`.

**What the census adds** (`formal-overlap-carriers-2026-10-04.md` §3.1). On
the standing corpus FP holds, so SC_all and BH hold; BH agrees with the
vertex-coincidence census, which records PPVC on every specimen. The cost sits in the strict
phase: unrealized carriers need `L` up to 12 inflations to reach offset zero,
realized ones at most 5, while `D - L <= 3` and `<= 6` respectively. The bound
`S(sigma)` of item 1 is valid but loose: on the Padovan/plastic control
`S = 14` while its carriers have `D - L <= 4`. Realization therefore matters
only in route B, where it shortens the strict phase; it changes neither the
target nor the remainder.

## 4. What this does not do

It proves neither SC_all nor BH for all PIP substitutions; both remain open
(BH is the realization-free PPVC of #139; SC_all is the all-pairs aligned
statement of #138's branch). Corollary FP′ inherits the review status of
Proposition V and Theorem S. The census numbers are finite evidence.

## 5. Verification

`mojo/tests/test_formal_overlap.mojo` pins `S = 14` on the plastic control and
checks `L <= D <= L + S` for each of its carriers through
`psc.formal_overlap.aligned_pair_depth`, which also checks that the formal graph
holds exactly the six aligned pairs.

## 6. Gap audit against Proposition V (2026-10-04)

The formal-overlap census and the vertex-coincidence box graph were built
independently. What is checked to agree, and what is not:

| Item | Status |
| --- | --- |
| Vertex sets | Carriers (region `K_T`, coincidences deleted) total 1,174,788 vertices on the standing corpus, equal to the box census's recurrent total; `tests/test_formal_overlap.mojo` checks state-for-state equality on two specimens. A per-specimen check over the whole corpus has **not** been run. |
| Covering regions | The canonical kernel now seeds from Proposition V's box; the oracle seeds from `K_T` (Cauchy–Schwarz on `q`). Both contain every cycle vertex, carriers do not depend on the region, and two differently seeded runs (float-sized, `K_T`) give the same 13,260 records; the box-seeded rerun is pending. |
| Depth conventions | `L` here is a per-carrier minimum of the first offset-zero depth, coincidences included; `K_V` is a per-vertex maximum of the first left-aligned depth. They are different statistics (max `L` = 12, max `K_V` = 17) and must not be compared as equals. |
| Recurrent-vertex conventions | §5.6b of the vertex note excludes every offset-zero vertex from "recurrent"; carriers keep the aligned pairs `(i, j, 0)` that lie on cycles (the 4,860 aligned carriers). |
| BH ⟺ PPVC | (⇐) PPVC gives an offset-zero descendant to every box vertex (Proposition V(2)), and cycle vertices are box vertices (V(1)). (⇒) If every cycle vertex has one, so does every box vertex: the box vertices without one form a finite child-closed set, which would contain a cycle. Then V(2) gives PPVC. Both directions of V(2) rest on Theorem B (unreviewed). |
| Mass lemma | Uses children counted with multiplicity; both constructions use the same kernel (`build_overlap_graph_from_seeds`), so the multiplicities agree. |
| Domains | FP and the carriers are surveyed only on the standing corpus; PPVC also on total length ≤ 8 and images ≤ 4. SC_all, and hence FP, is **not** checked beyond the standing corpus. |
| Realization × trichotomy | The realized/unrealized split of carriers is not cross-tabulated with the cases of §5.6b; whether unrealized strict carriers concentrate in the catch-up-free case is open. |

