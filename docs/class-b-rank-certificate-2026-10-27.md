# Class B top layer: a piecewise rank with symbolic occurrence edges (g=1, both branches)

**Status:** conditional, computer-assisted (exact executable all-parameter
certificates on the plus and minus g=1 rays); hypotheses (H1) and (H2) are open
and only finitely replayed (plus q=10..42, minus q=16..42); independent human
review pending.

## Target and literature stop/go

This is the "joint piecewise-rank/occurrence synthesis" that the
[label-ray note](class-b-label-rays-2026-10-23.md) redirected to after its
bounded depth envelopes refused 99 of 389 intervals and 202 selected shortest
edges failed strict decrease. It stays inside the finite exact program authorized
by the [top-layer stop/go](class-b-top-layer-stopgo-2026-10-23.md) and reuses
its source review (BBJS, Minervino–Thuswaldner, Akiyama–Gähler–Lee; AL11, CS01,
MT14 in [issue-84 sources](../sources/issue-84/README.md)) and the
[Theorem C method](p1b-symbolic-cone-2026-10-08.md). No new universal invariant
is proposed: a rank function on a residue ray is the standard ranking-function
proof of reachability, and the construction below changes only its finite
representation. Decision: **go** for an exact all-parameter rank on one ray,
with the two graph hypotheses kept explicit.

## Setting

Plus branch, gap g=1 (p=3q+11), residue 0, so the ray parameter is q itself;
floor q0=10 (the q=9 member has a non-affine edge-domain endpoint, see below).
Labels are `(top,bottom,k,c,y)` with typed coordinates `s=3k+c+y`, `d=c−3k`
as in the label-ray note. A *piece* is `(top,bottom,s,d; lo(t) ≤ k ≤ hi(t))`,
`t=q−q0`, with integer-affine ends; the offset-zero target labels `(t,b,0,0,0)`
are one-point pieces.

## Symbolic edges

For an actual edge from parent `(T,k)` to child `(T',k')`, the occurrence
identity of the label-ray note gives `k' = s − k + Δx` with
`Δx ∈ {−1,0,1}` (the difference of the x-coordinates of the two proper
prefixes). Hence an actual edge is determined, as a map on labels, by the
**symbolic edge** `(P → Q, Δx)`: parent piece, child piece, Δx. The map
`k ↦ s+Δx−k` has slope −1 in k and slope 0 in q.

Native all-edge exports (`class_b_label_rays.mojo plus 1 Q edges`) for
q=10..26 contain exactly 4,953 symbolic edges over 403 pieces. Every one acts on
a contiguous parent sub-interval whose endpoints are exactly affine in q on the
whole window (zero refusals from q0=10; at q0=9 two keys have a non-affine floor).

## Why one affine potential per interval cannot work

The first attempt imposed one `X = a q + b k + c` per carrier interval and
chose edges by a 0/1 MILP (403 pieces, 4,953 binaries, 1,779 coverage sets). It
reached its 15-minute limit without a feasible point. The data explain why. On
the type `(0,2,0,−4)` interval (`k ∈ [−t−14, t+14]`) first-hit depth is
V-shaped, about `|k|/2`: the wing `k<0` descends along one symbolic edge, the wing
`k>0` along another, and the chains on each wing are about `|k|/2` long. Any rank
must then grow in both directions from the middle, which no affine function of
k does. Exact depth is not piecewise affine with boundedly many pieces either:
about 100 intervals carry 10–30 parity zig-zag runs whose number grows with q.
This is the mechanism behind the 99 envelope refusals of the label-ray note.

## Construction

1. **Segments.** Each piece is cut at every symbolic edge-domain endpoint. All
   cut orders are stable for every t ≥ 0, giving 1,787 segments, none empty at
   the floor. Each segment gets its own integer potential `X_S = a q + b k + c`.
2. **Policy.** On 1,699 segments some edge lowers first-hit depth at every
   training point; that edge is the first choice. The remaining 80 segments
   (60 with parity zig-zag, 20 whose depth-guided edge splits non-uniformly over
   the child's segments) are completed greedily, keeping only options that leave
   the LP feasible. All 80 were resolved.
3. **Sub-edges.** A chosen edge is split along the segments of its child piece,
   so every certificate edge maps its parent domain into one child segment.
4. **Integer potentials.** With the policy fixed, a pure integer program gives
   `|a|,|b| ≤ 60`, `|c| ≤ 587`.

Steps 1–4 are a bounded synthesis prototype
(`oracles/python/class_b_rank_synthesis.py`, scipy/HiGHS). Floating solutions
only propose; nothing is accepted without the exact checks below. Two runs
produced byte-identical certificates on each ray.

## What is checked exactly, for every integer t ≥ 0

`kernel/psc/class_b_rank_certificate.mojo` (canonical) checks:

* every piece is nonempty, same-type pieces are disjoint and ordered, and
  `X ≥ 0` on every piece;
* every edge domain is a nonempty part of its parent piece, and its image under
  `k ↦ s+Δx−k` lies in its child piece;
* `X_child(q,k') ≤ X_parent(q,k) − 1` on every edge domain;
* the edge domains of every non-target piece cover it.

The inequalities are affine on the polyhedron `{t ≥ 0, lo(t) ≤ k ≤ hi(t)}`, so
they are checked at its two vertices and on its two recession rays `(1, slope)`.
Coverage is an exact sweep at every t up to one past the last crossing of any two
endpoint functions. After that crossing every comparison made by the sweep is
constant (here the horizon is t=1, since segment ends are edge-domain ends).

`oracles/python/class_b_rank_certificate_oracle.py` re-derives the same conditions
independently. Each endpoint value is an affine function of t, and coverage is
brute-forced to its own horizon `|Δv0|+2` over all endpoint pairs.

## Conditional statement

**Proposition (conditional, every q ≥ 10).** Let q ≥ 10 on the plus g=1 ray
and let G_q be the seed overlap graph. Assume

* **(H1) carrier inclusion:** every vertex of G_q lies in a certificate piece;
* **(H2) symbolic edges are actual:** for every certificate edge and every
  vertex of G_q in its domain, the edge's child label is an actual child in G_q.

Then every vertex v of G_q reaches offset zero in at most `X(v)` steps.

*Proof.* By coverage, every non-target vertex v lies in the domain of some
certificate edge. By (H2) its child w is a vertex, and by the descent condition
`X(w) ≤ X(v) − 1`. By (H1) w again lies in a piece, and X is a nonnegative
integer there. The descent therefore stops after at most X(v) steps, and it can
stop only at a vertex that needs no edge, that is, a target piece. ∎

(H1) and (H2) are the remaining **geometric** obligations: all-child closure and
seed inclusion for the carrier, and strict real overlap along each symbolic
occurrence, uniformly in q. They are not proved here.

## Finite evidence for the hypotheses

Native exports q=10..42 (training 10..26, holdout 27..42) replay under both
checkers with identical lines: at every member the vertex set **equals** the
carrier (zero carrier points without a vertex), and every non-target vertex is
checked on its chosen actual edge (`edges_checked = vertices − 8`). On these
members X dominates first-hit depth everywhere. It is a loose step bound:
max X is 2,648 against depth 27 at q=42, because the coefficient budget ±60 is
saturated and the objective does not seek tightness.

## Transfer to minus g=1

The same generator, changed only by the two fixes below, was run on minus g=1
(p=3q−1, residue 0): training q=16..30 (the label-ray training bound for this
line), holdout q=31..42. The vertex sections of all 28 new native `edges`
exports (q=15..42) equal the committed label-ray exports byte-for-byte.

* **Floor.** At the label-ray floor q=15 two segments, in types (0,2,−1,−6)
  and (2,0,1,6), are empty: they are `[−q+3, −13]` and `[13, q−3]`, nonempty
  only from q=16, so their edges are absent at q=15. The prototype now refuses
  a segment that is empty at the floor; the rank floor is q0=16, one above the
  label-ray floor, as q0=10 is on plus.
* **Order.** Interleaving greedy completions with depth-guided choices in
  index order refused (segment 249 had no LP-feasible option). Fixing every
  depth-guided choice first, as the plus scratch run did, succeeds. The plus
  certificate was regenerated with this generator: the same 1,787 segments and
  2,302 edges with different integer potentials, and identical replay lines.

Result: 431 pieces, 4,484 symbolic edges and 1,301 segments (1,165
depth-guided, 128 completed), integer potentials with `|a|,|b| ≤ 60` and
`|c| ≤ 758`, and 1,970 certificate edges. It passes the exact all-parameter
check (coverage horizon t=1) and the oracle. Replays on q=16..42 pass under
both checkers, with vertex set = carrier at every member; max X is 2,302
against depth 27 at q=42. The conditional proposition above holds verbatim on
the minus g=1 ray for q ≥ 16, with (H1) and (H2) read there. The q=15 member is
a complete finite graph whose hitting is already recorded in the label-ray
packet; this certificate does not cover it.

## Negative controls

Native and oracle tests share a toy certificate: one type, wings
`[−t−2,−1]`, `[1,t+2]`, target `k=0`, `X=|k|`, laps translating k by 2. Each
of six tamperings refuses with the condition it breaks: vertex decrease, ray
decrease, a missing edge (coverage), Δx moving the image out of its child,
negative potential, and a dropped target flag. Replays refuse when an actual edge
behind a chosen symbolic edge is deleted from a real q=10 export, and when a
vertex lies outside every piece.

## Non-claims

* No boundary-hitting, G1 or PSC claim is promoted. The propositions are
  conditional on (H1) and (H2) for all q ≥ 10 (plus) and q ≥ 16 (minus); both
  are verified only for q ≤ 42.
* Only the two g=1 rays are treated. The other 19 residue rays of the
  label-ray note (g ≥ 2) are untouched; whether the method transfers there is
  open.
* The floors q0=10 and q0=16 are where each synthesis window starts, not proved
  stabilization thresholds; q=9 (plus) and q=15 (minus) are excluded.
* Pieces, symbolic edges and segments were fitted on q=10..26 (plus) and
  q=16..30 (minus) only. Holdouts test them; they do not prove them.
* The synthesis prototype is Python with floating solvers. It is not canonical
  and it decides nothing.

Replay commands, digests and logs are in
[the packet](../evidence/class-b-rank-certificate-2026-10-27/README.md).
