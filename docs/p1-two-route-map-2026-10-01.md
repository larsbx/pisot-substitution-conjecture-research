# P1 two-route attack map — 2026-10-01

**Status:** active research map for the two complementary branches of the
seedwise-overlap-productivity obstruction. It incorporates two new proved
reductions from this research branch:

1. the aligned branch is reduced to a fixed bad hub edge or one forced
   alternating type-E template;
2. the strict-zipper M-adic zero-class candidates obey exactly the existing
   overlap affine recurrence, so deeper finite-cokernel filtering alone is not
   a new closure mechanism.

Neither reduction closes #84.

## 1. Shared starting point

A failure of seedwise overlap productivity yields a finite child-closed
irreducible nonproductive overlap SCC (S) with

[
ho(N_S)=eta,qquad
N_SV_S=V_SM^{mathsf T},qquad
operatorname{rank}_{mathbb Q}V_S=3.
]

The existing boundary theorem then gives the exact split

[
A_+(S)
earnothing
quad	ext{or}quad
S	ext{ has no offset-zero vertex}.
]

The first case is the aligned route. The second is the strict-zipper route.
Right-aligned vertices do not alter this dichotomy; they are handled through
reversal and may coexist with the strict-zipper case.

The routes are complementary:

- eliminating the aligned route forces every bad SCC into the strict zipper;
- forcing one strict-zipper boundary hit sends a bad SCC into the aligned
  route;
- proving both eliminates every bad SCC and closes the one-seed productivity
  premise of Theorem 5.38.

## 2. Route A — aligned strong-coincidence propagation

### A0. Existing inputs

Fix a Barge–Diamond-good edge (G={a,b}) and complementary hub (c).

Already proved:

- a bad offset-zero pair is not eventually coincident;
- every deterministic first child remains bad and offset zero;
- no bad pair equals (G);
- hence every bad aligned pair lies in the two-edge hub star
  ({a,c},{b,c});
- endpoint types A/B synchronize and G is eliminated.

### A1. New milestone: complete recurrent pair-cycle normal form

The new aligned-cycle theorem in
docs/p1a-aligned-cycle-normal-form-2026-10-01.md proves that every recurrent
bad aligned first-child cycle is one of exactly two shapes:

**A1-fixed**
[
{a,c}mapsto{a,c}
quad	ext{or}quad
{b,c}mapsto{b,c}.
]

**A1-altE**
[
{a,c}longleftrightarrow{b,c},
]
which forces
[
h(c)=c,qquad h(a)=b,qquad h(b)=a.
]

Thus the only period-two aligned obstruction is endpoint type E with the
Barge–Diamond-good edge itself as the letter 2-cycle.

There is no period-three or longer aligned pair cycle.

Canonical Mojo exhausts all 81 endpoint-map/good-edge placements and pins:

- 45 with no viable bad orbit;
- 33 fixed-edge templates;
- 3 alternating-E templates.

### A2. Immediate new information in the exceptional template

In A1-altE the good edge (G) never synchronizes at the left endpoint:
its endpoint letters alternate forever.

Therefore its Barge–Diamond eventual-coincidence witness is necessarily at a
positive balanced prefix. The exceptional endpoint template consequently
comes with an **interior** equal-Parikh coincidence witness.

This turns the next problem from proving some coincidence exists into a
transport problem for a known interior witness.

### A3. Next proof targets

**A-fixed — fixed-edge interior forcing.**

Show that a setwise fixed bad hub edge cannot avoid every transported
Barge–Diamond interior witness in a closed nonproductive component.

The key missing object is a precise map from an equal-Parikh prefix witness in
one good-edge iterate to a zero-return boundary in descendants of the fixed bad
edge.

**A-altE — interior-witness transport.**

Use
[
h(c)=c,quad h(a)=b,quad h(b)=a
]
and the guaranteed interior witness for ({a,b}) to force that good edge to
appear at a zero-return boundary of a descendant of ({a,c}) or
({b,c}).

Either theorem eliminates its template immediately.

### A4. What not to do

Do not return to:

- a larger short-image coincidence census;
- endpoint synchronization as a substitute for eventual coincidence;
- a substitution-independent bound on raw matrix/digit height;
- a claim that the Barge–Diamond good pair is predetermined.

## 3. Route B — strict-zipper adelic hitting

### B0. Existing exact target

For a realized strict-zipper vertex ((i,j,w)), a boundary hit at level (m)
is exactly

[
M^m win D_m(i,j)=P_m(i)-P_m(j).
]

The full non-unit target lives in the Archimedean contracting embeddings plus
the finite places dividing ((eta)). An Archimedean-only collision is not
acceptance.

### B1. New milestone: finite-place zero-class filter

Define

[
Z_m(i,j)
={zinmathbb Z^3:M^mzin D_m(i,j)}.
]

A genuine hit implies its occurrence-labelled prefix difference is zero in

[
mathbb Z^3/M^mmathbb Z^3.
]

The new canonical M-adic diagnostic implements this exact necessary filter.

On the determinant-two golden regression, pair ((1,2)) at level two has
35 proper-prefix occurrence pairs and only 11 survive the zero class.

For unimodular Tribonacci all 12 level-two pairs in the selected regression
survive, correctly reflecting that the cokernel is trivial.

### B2. New milestone: the carry recursion is not a new dynamics

The M-adic carry theorem in
docs/p1b-madic-carry-reduction-2026-10-01.md proves

[
zin Z_{m+1}(i,j)
]

iff there are first-level child occurrences
(sigma(i)=pas), (sigma(j)=qbt) and (z'in Z_m(a,b)) with

[
z'=Mz+pi(q)-pi(p).
]

This is exactly the occurrence-labelled overlap child update.

Therefore descaled finite-place candidates are simply the reverse zero-offset
basin of the existing affine overlap graph.

**Consequence:** repeatedly strengthening only the M-adic quotient cannot close
#139. It prunes prefix pairs, but after descaling it reconstructs the same
affine state recurrence that the strict zipper already avoids.

This is a stop result for a potentially expensive dead end.

### B3. The remaining genuinely new theorem

The next step must add geometry not encoded by the affine carry graph:

> **Occurrence-compatible adelic coverage lemma.** A realized periodic orbit
> of a child-closed strict-zipper SCC must enter the graph-directed
> prefix-difference subtile corresponding to its reverse zero basin.

The proof must use the full non-unit representation or another complete
recurrence theorem. It cannot be replaced by:

- a deeper finite quotient;
- compactness alone;
- multiple tiling or positive measure;
- residual Perron criticality;
- bounded collars;
- closure of an untyped Rauzy-subtile difference.

## 4. Interaction of the routes

The two routes meet exactly at offset zero.

    bad SCC
      |
      +-- A_+(S) nonempty ---------------- Route A
      |
      +-- no offset-zero vertex ---------- Route B
                                            |
                                            | force boundary hit
                                            v
                                          Route A

Thus neither route has to prove the other route's internal theorem.

A complete proof can proceed in either order.

**A-first**

[
	ext{aligned branch impossible}
Rightarrow
	ext{every bad SCC strict}
Rightarrow
	ext{adelic hit}
Rightarrow
ot.
]

**B-first**

[
	ext{every strict SCC hits offset zero}
Rightarrow
	ext{every bad SCC aligned}
Rightarrow
	ext{aligned propagation}
Rightarrow
ot.
]

## 5. Research priority after the present milestone

The best immediate theorem target is **A-altE interior-witness transport**.

Reasons:

1. it is the smallest remaining aligned template;
2. unlike the fixed-edge case, it supplies a guaranteed *interior* good-pair
   witness;
3. it is purely discrete/combinatorial and does not require local-field
   infrastructure;
4. a proof would remove the only non-fixed aligned pair cycle.

In parallel, Route B should now skip further quotient depth and move directly
to the graph-directed adelic coverage interface.

## 6. Review milestone

The present branch is ready for mathematical review when the following are
confirmed:

- the hand proof of the fixed-edge/alternating-E aligned normal form;
- the exhaustive Mojo counts 45 / 33 / 3;
- the M-adic zero-class filter's exact non-unit and unimodular regressions;
- the proof that descaled M-adic candidates obey the same affine child
  recurrence;
- the conclusion that deeper finite-cokernel refinement alone is not an
  independent closure strategy.

Acceptance of those points changes the research frontier even though it does
not yet change the theorem status of #84.
