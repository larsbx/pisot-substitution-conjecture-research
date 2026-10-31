# All E6 direct children are forward-X accessible: one-state nine-seed closure reduction

**Status:** exact all-parameter *scoped arithmetic derivation* for
the minus class-A chamber, stacked on #428 (nine seeds -> X) and
#430 (X -> eight non-E6 seed vertices). No independent human review
or fresh hosted exact-head acceptance yet. The graph-closure conclusion
is **conditional on those predecessor certificates and the precise E6
complete-star classification**, not a G1/BH/#139/PSC theorem.

## The actual exceptional seed is E6, not a new state

For k,t>=0 put n=k+t+3, d=k+2t+5, A=n+d, N=n-1,
with x->x y^A x, c->c y^n x, y->x y^N c.

The ninth swapped-patch source from #428 is
S1=E6=(x,x,0,1,0), the same oriented full-Parikh state
as research PR #382's E6. Its physical shift is
b=Lc/Ly=1+h, where h=1/beta, Ly=1, Lx=2+rho.
The inflated shift is **G=beta+1=n+3+alpha**,
where alpha=rho+h, and the inherited root inequalities
give 0<h<1/5, h<rho and rho+2h<1.

The full nine-kind E6 strict-star classification
already appears in #382. It is repeated here **only as a
focused source-interface derivation**, without transplanting
the old staged kernel or duplicate proof-bank receipt:

| Actual occurrence kind | Exactly accepted indices | Full typed target |
| --- | --- | --- |
| RUN/FIRST | (i,0), i=n+2..n+4 | (y,x,0,1,n-i+1), r=-1,-2,-3 |
| RUN/RUN | i-j=n+3, 1<=j<=d-3 | (y,y,1,1,-3) |
| RUN/RUN | i-j=n+4, 1<=j<=d-4 | (y,y,1,1,-4) |
| LAST/RUN | (A+1,j), j=d-3..d-1 | (x,y,1,1,j-d-1), r=-4,-3,-2 |

All remaining five kinds are strictly disjoint. The exact
physical expressions are
D_RF=n+2+h-i,
D_RR=n+3+alpha+j-i,
D_LR=j-d+2+alpha.
Their strict inequalities select precisely the displayed
integer ranges; FF/FR/FL/RL/LL lie too far right, and
LAST/FIRST has D=1+h-d<-Lx since d>=5.
Every index is a genuine literal RUN or LAST occurrence.
The actual incidence/prefix rule
w'=Mw+P_bottom-P_top gives the full typed tuples.

Consequently, **for all k,t>=0** E6 has exactly
3+(d-3)+(d-4)+3 = **2d-1 indexed strict children**
and just **eight distinct typed child labels** per
orientation (sixteen across the true reversal). The
strict star does **not** have E6 as one of its children.

The eight target labels, simultaneously present in every
member, are:

    (y,x,0,1,-3), (y,x,0,1,-2), (y,x,0,1,-1),
    (y,y,1,1,-4), (y,y,1,1,-3),
    (x,y,1,1,-4), (x,y,1,1,-3), (x,y,1,1,-2).

These tuples, rather than historical names, are canonical.

## Uniform constructive X -> each of the eight E6 targets

For every integer k,t>=0, the new source constructs
actual, strictly overlapping indexed paths from
X=(x,x,1,0,-1) to all eight targets.
The only parameter split is **t=0 versus t>=1**:

| Child type | t=0 forward-X path | t>=1 forward-X path |
| --- | ---: | ---: |
| Three y/x labels (offsets 0,1,-3/-2/-1) | 3 edges each | 3 each |
| Two y/y labels (offsets 1,1,-4/-3) | 3 each | 3 each |
| Three x/y labels (offsets 1,1,-4/-3/-2) | 3 each | 5 each |

All paths begin
X --(d+2,0)--> (y,x,0,-1,0).
Five of them continue through (x,y,0,-1,2) and
then select a final indexed child; the three x/y
cases take a distinct t=0 LAST path or a
five-edge t>=1 typed route. The complete
ordered-word indices and typed intermediate
five-tuples are given in the source's
EDGE_T0 / EDGE_T1PLUS and PATH_T0 / PATH_T1PLUS,
not inferred from a quotient graph.

There are 16 (parameter-chamber,child-label) cases and
**108 exact directed symbolic path-edge checks**
counting genuine reversals. The checker verifies
every true FIRST/RUN/LAST type, each affine index bound
at the chamber corner and in both unbounded directions,
and the coefficientwise integer identity in Z[k,t]
for **every** selected transition.

Its 28 distinct oriented path states have **56 strict
physical overlap margin certificates** from the four
rational closure vertices of the inherited
(h,rho) root chamber. No floating approximations
or tile-length independence hypotheses are used.

Separate exact literal-prefix/Fraction validation
over 117 parameter members and both orientations:
**297,648 E6 candidate word pairs**,
**8,658 actual strict indexed E6 children**,
and **6,864 true oriented X-to-child path-edge replays**.
Five locally executed tests pass. The new source and
tests are committed byte-identically to the local
execution. These finite counts are independent
regression evidence, not the basis of universal
integer-cone quantification.

## Precise graph-theoretic consequence

Let S be the **nine strict swapped-patch overlap seeds**
of #428, and R(X) the complete **forward** closure of
X in the strict, coincidence-terminalized overlap
graph at a fixed k,t. Let E denote S1=E6.

Once the accepted all-parameter actual occurrence
certificates from #428 and #430 are combined with the
E6 star and eight X-to-child certificates here, then

    Reach(S) = Reach(X) U {E}.

Why: #428 gives each seed a path to X, hence
Reach(X) subset Reach(S). #430 places all eight
seeds other than E inside Reach(X). This packet
shows every **actual** E child lies in Reach(X);
since Reach(X) is forward-closed, the union
Reach(X) U {E} is forward-closed and contains
all nine seeds, yielding the reverse inclusion.
No graph finiteness assumption is required for
this elementary set equality.

The identity is compatible with the exact
(k,t)=(3,0) counter-calibration: E is **not**
in Reach(X) there and is the sole extra vertex.
At other finite parameters E can already belong
to Reach(X), giving equality without an extra vertex.

**The remaining central obligation is NOT removed:**
prove that every nonterminal vertex in Reach(X)
can reach a typed coincidence (or equivalently,
rule out a closed nonproductive recurrent component
in the relevant complete graph). Knowing
every seed reaches X or that every E child belongs
to Reach(X) does not establish that every state
**reachable from X** returns to it or to a coincidence.
Nor does this nine-seed graph automatically cover all
literature-realized overlaps or strict-zipper classes.
General BH/#139, G1, A1-prime, PDS and PSC remain open.

## Integration and provenance firewall

PR #382's original E6 star and every-first-choice
productivity packet remains a research-only separate
derivation. This focused change adds no duplicate
E6 Mojo kernel, modifies no existing receipts or
governed claim statuses, and does not merge old
stack branches. The new all-parameter path proof is
stacked on #430 -> #428; integrate strictly in
dependency order after fresh hosted checks and
independent human review. The complete E6 star
count and typed image are independently rechecked,
but no finite output substitutes for the universal
nine-kind physical inequalities displayed above.
