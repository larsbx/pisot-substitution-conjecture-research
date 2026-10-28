# Class B top layer: piecewise ranks with symbolic occurrence edges on all 21 residue rays

**Status:** conditional, computer-assisted (exact executable all-parameter
certificates on all 21 residue rays of the class-B top layer: plus g=1..5,
minus g=1..3); hypotheses (H1) and (H2) are open and only finitely replayed
(every member from each floor through q=48); independent human review pending.

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
representation. Decision: **go** for exact all-parameter ranks, one per residue ray,
with the two graph hypotheses kept explicit.

## Setting

The 21 residue rays are those of the label-ray note: branch plus (p=3q+12−g,
g=1..5) or minus (p=3q−g, g=1..3), residue r = q mod g, parameter
`t = (q − q0)/g` on the members `q = q0, q0+g, …`. Labels are
`(top,bottom,k,c,y)` with typed coordinates `s=3k+c+y`, `d=c−3k` as in the
label-ray note. A *piece* is `(top,bottom,s,d; lo(t) ≤ k ≤ hi(t))` with
integer-affine ends; the offset-zero target labels `(t,b,0,0,0)` are one-point
pieces. The construction is first described on plus g=1 (q0=9), where it was
developed; the other 20 rays use it unchanged.

## Symbolic edges

For an actual edge from parent `(T,k)` to child `(T',k')`, the occurrence
identity of the label-ray note gives `k' = s − k + Δx` on both branches, with
`Δx ∈ {−1,0,1}` (the difference of the x-coordinates of the two proper
prefixes; ε enters only `s'`). Hence an actual edge is determined, as a map on
labels, by the **symbolic edge** `(P → Q, Δx)`: parent piece, child piece, Δx.
The map `k ↦ s+Δx−k` has slope −1 in k and slope 0 in q.

Native all-edge exports (`class_b_label_rays.mojo plus 1 Q edges`) on plus g=1
contain 4,951 symbolic edges over 403 pieces on the training window q=9..26
whose parent sets are contiguous with exactly affine ends. Two further keys are
uniform on q=10..26 but not from q=9; the synthesis leaves them out and does not
need them.

## Why one affine potential per interval cannot work

The first attempt imposed one `X = a q + b k + c` per carrier interval and
chose edges by a 0/1 MILP (403 pieces, 4,953 binaries, 1,779 coverage sets, on
q=10..26). It reached its 15-minute limit without a feasible point. The data
explain why. On the type `(0,2,0,−4)` interval (`k ∈ [−q+…, q−…]`) first-hit
depth is V-shaped, about `|k|/2`: the wing `k<0` descends along one symbolic
edge, the wing `k>0` along another, and the chains on each wing are about
`|k|/2` long. Any rank must then grow in both directions from the middle, which
no affine function of k does. Exact depth is not piecewise affine with boundedly
many pieces either: about 100 intervals carry 10–30 parity zig-zag runs whose
number grows with q. This is the mechanism behind the 99 envelope refusals of
the label-ray note.

## Construction

1. **Segments.** Each piece is cut at every symbolic edge-domain endpoint. All
   cut orders must be stable for every t ≥ 0 and no segment may be empty at the
   floor (both refuse otherwise). On plus g=1 this gives 1,787 segments. Each
   segment gets its own integer potential `X_S = a q + b k + c`.
2. **Policy.** Where some edge lowers first-hit depth at every training point of
   a segment, that edge is fixed first (1,677 segments on plus g=1). The rest
   (102: parity zig-zag, or a depth-guided edge that splits non-uniformly over
   the child's segments) are then completed greedily, keeping only options that
   leave the LP feasible.
3. **Sub-edges.** A chosen edge is split along the segments of its child piece,
   so every certificate edge maps its parent domain into one child segment.
4. **Integer potentials.** With the policy fixed, a pure integer program gives
   coefficients within `|a|,|b| ≤ 60`.

Steps 1–4 are a bounded synthesis prototype
(`oracles/python/class_b_rank_synthesis.py`, scipy/HiGHS). Floating solutions
only propose; nothing is accepted without the exact checks below. A second run
reproduced every certificate byte-for-byte.

## What is checked exactly, for every integer t ≥ 0

`kernel/psc/class_b_rank_certificate.mojo` (canonical) checks:

* every piece is nonempty, same-type pieces are disjoint and ordered, and
  `X ≥ 0` on every piece;
* every edge domain is a nonempty part of its parent piece, and its image under
  `k ↦ s+Δx−k` lies in its child piece;
* `X_child(q,k') ≤ X_parent(q,k) − 1` on every edge domain;
* the edge domains of every non-target piece cover it.

The inequalities are affine on the polyhedron `{t ≥ 0, lo(t) ≤ k ≤ hi(t)}`, so
they are checked at its two vertices and on its two recession rays
`(1, slope)`, where one step in t moves q by g. Coverage is an exact sweep at
every t up to one past the last crossing of any two endpoint functions. After
that crossing every comparison made by the sweep is constant (here the horizon
is t=1 on every ray, since segment ends are edge-domain ends).

`oracles/python/class_b_rank_certificate_oracle.py` re-derives the same conditions
independently. Each endpoint value is an affine function of t, and coverage is
brute-forced to its own horizon `|Δv0|+2` over all endpoint pairs.

## Conditional statement

**Proposition (conditional, every member at or above the floor).** Fix one of
the 21 residue rays with its certificate floor q0, let q ≥ q0 be a member, and
let G_q be the seed overlap graph. Assume

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

## All 21 rays

The generator was run on every ray with one rule: start at the label-ray floor,
train on members q ≤ 30 (plus g=1: q ≤ 26, its label-ray training bound), and
raise the floor by one period only when the synthesis refuses. Native exports
were made for every member through q=48, the exporter's limit; the members
q=43..48 lie beyond the label-ray packet and are holdouts for the carriers as
well as for the ranks. On all 8 lines the vertex sections of the exports
through q=42 equal the committed label-ray exports byte-for-byte.

| Ray | Label floor | Rank floor | Training | Replayed (members) | Holdout | Segments | Guided / completed | Edges | Max X / depth (last) |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| plus-g1-r0 | 9 | 9 | 9..26 | 9..48 (40) | 22 | 1,787 | 1,677 / 102 | 2,296 | 3,008 / 30 |
| plus-g2-r0 | 12 | 12 | 12..30 | 12..48 (19) | 9 | 1,025 | 945 / 72 | 1,274 | 1,506 / 17 |
| plus-g2-r1 | 11 | 11 | 11..29 | 11..47 (19) | 9 | 1,035 | 947 / 80 | 1,265 | 1,506 / 16 |
| plus-g3-r0 | 12 | 12 | 12..30 | 12..48 (13) | 6 | 729 | 651 / 70 | 877 | 1,024 / 12 |
| plus-g3-r1 | 16 | 16 | 16..28 | 16..46 (11) | 6 | 773 | 697 / 68 | 915 | 966 / 12 |
| plus-g3-r2 | 14 | 14 | 14..29 | 14..47 (12) | 6 | 723 | 647 / 68 | 873 | 966 / 13 |
| plus-g4-r0 | 16 | 16 | 16..28 | 16..48 (9) | 5 | 609 | 527 / 74 | 766 | 724 / 10 |
| plus-g4-r1 | 17 | 17 | 17..29 | 17..45 (8) | 4 | 581 | 501 / 72 | 731 | 664 / 10 |
| plus-g4-r2 | 18 | 18 | 18..30 | 18..46 (8) | 4 | 579 | 499 / 72 | 731 | 724 / 9 |
| plus-g4-r3 | 15 | 15 | 15..27 | 15..47 (9) | 5 | 639 | 553 / 78 | 782 | 724 / 10 |
| plus-g5-r0 | 20 | 20 | 20..30 | 20..45 (6) | 3 | 556 | 464 / 84 | 692 | 544 / 8 |
| plus-g5-r1 | 16 | 16 | 16..26 | 16..46 (7) | 4 | 526 | 430 / 88 | 652 | 544 / 8 |
| plus-g5-r2 | 17 | 17 | 17..27 | 17..47 (7) | 4 | 524 | 428 / 88 | 654 | 544 / 8 |
| plus-g5-r3 | 18 | 18 | 18..28 | 18..48 (7) | 4 | 500 | 406 / 86 | 630 | 544 / 9 |
| plus-g5-r4 | 19 | 19 | 19..29 | 19..44 (6) | 3 | 500 | 408 / 84 | 636 | 544 / 8 |
| minus-g1-r0 | 15 | 16 | 16..30 | 16..48 (33) | 18 | 1,301 | 1,165 / 128 | 1,970 | 2,662 / 30 |
| minus-g2-r0 | 18 | 20 | 20..30 | 20..48 (15) | 9 | 748 | 626 / 114 | 1,158 | 1,264 / 16 |
| minus-g2-r1 | 17 | 19 | 19..29 | 19..47 (15) | 9 | 764 | 640 / 116 | 1,172 | 1,264 / 16 |
| minus-g3-r0 | 18 | 24 | 24..30 | 24..48 (9) | 6 | 590 | 522 / 60 | 839 | 844 / 12 |
| minus-g3-r1 | 16 | 22 | 22..28 | 22..46 (9) | 6 | 630 | 552 / 70 | 873 | 785 / 12 |
| minus-g3-r2 | 17 | 23 | 23..29 | 23..47 (9) | 6 | 606 | 532 / 66 | 855 | 785 / 11 |

Every certificate passes the exact all-parameter check and the oracle. Every
replay of all 271 members passes under both checkers with identical lines; at
each the vertex set **equals** the carrier and every non-target vertex is
checked on its chosen actual edge. X dominates first-hit depth everywhere, as a
rank must, but loosely: the objective does not seek tightness and `|b|`
saturates the ±60 budget on every ray.

**Floors.** On plus every rank floor equals the label-ray floor. On minus it is
one period higher for g=1, 2 and two periods higher for g=3. Each skipped
floor is refused by the synthesis because a segment is empty there; on minus
g=1, for instance, `[−q+3, −13]` in type (0,2,−1,−6) and `[13, q−3]` in type
(2,0,1,6) are nonempty only from q=16, so their edges are absent at q=15.
`rays.json` records the refusal text for every skipped floor. The members
below a rank floor are complete finite graphs whose hitting is recorded in the
label-ray packet; the certificates do not cover them.

**History.** The plus g=1 certificate was first built from q0=10, because the
exploratory run saw two non-affine edge-domain keys at q=9. The final generator
drops such keys and succeeds from q=9, so the certificate now starts at the
label-ray floor. Two generator fixes came from the minus g=1 transfer: refusing a
segment that is empty at the floor (instead of a later "no option" refusal), and
fixing every depth-guided choice before any greedy completion; interleaving them
in index order made segment 249 of minus g=1 infeasible.

**Thin windows.** For g ≥ 4 and on minus g=3 the training windows hold only 3–4
members per ray, and the holdouts 3–6. The replays are exact, but the affine
fits behind pieces and symbolic edges rest on few points there.

## Negative controls

Native and oracle tests share a toy certificate: one type, wings
`[−t−2,−1]`, `[1,t+2]`, target `k=0`, `X=|k|`, laps translating k by 2. Each
of six tamperings refuses with the condition it breaks: vertex decrease, ray
decrease, a missing edge (coverage), Δx moving the image out of its child,
negative potential, and a dropped target flag. Replays refuse when an actual edge
behind a chosen symbolic edge is deleted from a real q=9 export, and when a
vertex lies outside every piece.

## Non-claims

* No boundary-hitting, G1 or PSC claim is promoted. Each proposition is
  conditional on (H1) and (H2) for every member at or above its floor; both are
  verified only for members q ≤ 48.
* The floors are where each synthesis window starts, not proved stabilization
  thresholds; members below them are excluded.
* Pieces, symbolic edges and segments were fitted on the training windows only.
  Holdouts test them; they do not prove them.
* The class-B top layer is covered ray by ray; a g-uniform certificate, and the
  class-B layers below the top layer, are not addressed.
* The synthesis prototype is Python with floating solvers. It is not canonical
  and it decides nothing.

Replay commands, digests and logs are in
[the packet](../evidence/class-b-rank-certificate-2026-10-27/README.md).
