# Orientation-complete swapped-patch closure: at most E6 and R(E6) outside Reach(X)

**Status:** a finite exact graph census plus a general conditional
reversal/union lemma. The universal minus-class-A conclusion depends on
the *unaccepted* all-parameter certificates in #428, #430, #431 and #432.
It is not an accepted mainline theorem, all-descendant productivity,
literature-realized overlap coverage, BH/#139, G1, A1-prime or PSC.

## Correct set of initial oriented overlaps

For integer k,t>=0, n=k+t+3, d=k+2t+5 and the actual words
x->x y^(n+d) x, c->c y^n x, y->x y^(n-1) c,
a strict oriented overlap is the full tuple
(top,bottom,dx,dc,dy) with actual integer
bottom-minus-top Parikh displacement.

The earlier nine-source construction used the oriented
overlaps of aligned *ab/ba* for unordered a<b.
A genuinely reversal-complete version must also include
the nine reverse-oriented states of *ba/ab*.
The two sets are disjoint: **18 distinct initial strict sources**.
The reversal involution sends (a,b,p,q,r) to
(b,a,-p,-q,-r), and swaps actual indexed child occurrences.

Write X=(x,x,1,0,-1) and E=E6=(x,x,0,1,0).
Its reversed orientation R(E)=(x,x,0,-1,0)
is a **different actual vertex**, even though the tile
types agree. It may not be silently identified with E.

## Conditional universal set identity, no finiteness assumed

Let S9 be the original nine oriented sources,
S18=S9 U R(S9), and U=Reach(X) in the
**actual complete strict overlap graph**, with typed
zero-offset coincidences optionally terminalized
in both orientations consistently.

Four external, independently specified premises are:

1. #428: each original nine source can reach X.
2. #430: X reaches each of the eight original
   sources other than E.
3. #431: all actual E children lie in U,
   giving Reach(S9)=U U {E}.
4. #432: X↔R(X) and reversal covariance,
   proving R(U)=U. Since reversal is a
   graph automorphism,
   Reach(R(S9))=R(Reach(S9)).

Taking the union proves, **conditional on these accepted source
proofs**, the exact all-parameter oriented closure reduction

    Reach(S18) = Reach(X) U {E, R(E)}.

This is a valid graph identity independently of the
number of overlap states, cyclic structure, finiteness,
or a particular chosen finite seed-graph cap.

Because E reaches X by #428, R(E) reaches R(X)
by reversal, and R(X) reaches X by #432.
Consequently the predicate

    every vertex of Reach(S18) admits a path
    to a typed coincidence

is equivalent, *under these same hypotheses*, to

    every vertex of Reach(X) admits such a path.

Neither predicate is proved by the set identity.
A path from X to some coincidence or productivity of
the 18 starting sources alone is insufficient.

## Exact finite independent census and negative controls

The new main-based oracle
oracles/python/class_a_oriented_swap_closure.py
constructs all **complete actual strict indexed child edges**
using the existing unchanged repository
class_a_boundary_children.py Fraction geometry.
It never reports a verdict from a capped partial graph;
typed full-zero coincidence vertices are terminalized
for existential productivity only.
It then computes Reach(X), Reach(S9), Reach(R(S9))
and Reach(S18) **within the same graph**, and
checks the actual reversal/closure identities.

All 16 exact completed graphs 0<=k<=3,0<=t<=3 pass.
The full 18-source graph counts are:

| k | t=0 | t=1 | t=2 | t=3 |
| ---: | ---: | ---: | ---: | ---: |
| 0 | 784 | 1010 | 1220 | 1440 |
| 1 | 436 | 642 | 646 | 836 |
| 2 | 378 | 390 | 594 | 568 |
| 3 | 352 | 342 | 362 | 548 |

Each specimen's complete graph has either **zero**
vertices outside U or **exactly two**:
E=(x,x,0,1,0) and R(E)=(x,x,0,-1,0).
No other extra labels occur in those completed specimens.

At (k,t)=(3,0), in particular:
Reach(X) has 350 vertices,
Reach(S9) has 351 vertices and
Reach(S18) has **352** vertices.
The two extra vertices are precisely E and R(E).
This is a direct negative control against treating
the earlier one-exception **nine-orientation** graph
as already reversal-complete.

The general graph implication has explicit negative
tests for a missing seed, missing reversed closure,
a non-reversal-invariant X closure and an extra unregistered
vertex. The finite builder rejects invalid source geometry,
negative parameters and truncated caps. The four local
regression tests pass using the original Geometry
contract faithfully mirrored; hosted exact-head CI against
the repository's unchanged oracle remains pending.

## Remaining mathematical task

The true substantial open gate, in this exact minus-class-A
source system, is still:

    every nonterminal vertex in Reach(X)
    admits an occurrence-indexed path to typed coincidence.

The finite observations of a giant productive recurrent
X-containing SCC do not prove this uniformly over k,t.
Reversal-invariant forward closure is not proof that every
state *returns to X*, and no literature-realized-overlap
coverage transfer is established. Do not promote PSC or BH.
