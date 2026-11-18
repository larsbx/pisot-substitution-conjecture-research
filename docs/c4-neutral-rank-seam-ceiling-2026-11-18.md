# Corrected neutral rank: seam ceiling, a positive `+1` control, and the endpoint branch

**Status:** Two written lemmas with exact bounded Mojo controls, one new
literal negative control, and a census of a source-only quantity. Lemma B's
algebraic and combinatorial core, T6, the spectral step of the #601 cycle
theorem, Lemma A's orbit law and ceiling, and the `01/122/201` witness with
its single interior $4$-cycle are machine-checked in Lean
(`PscVerif.NeutralRankSeam`, `NeutralRankSeamCycle`, `SeamCycleSpectrum`). Both
lemmas are conditional on a strict rank-two component, which no tested
specimen has. Independent review is pending. Neither lemma excludes the
neutral weight. Universal C4 and PSC remain open, and this note registers
no governed claim.

**Relation to #604.** [#604](c4-neutral-rank-obstruction-2026-11-17.md),
merged first, was developed in parallel. It proves Lemma A in closed form
as the orbit budget $B_\varepsilon(q)=m(H_1(E))-\mathbf 1_{\delta=1}$
with the positive-part envelope $U_\varepsilon$; it uses connectedness of
the eventual range $E$ and surjectivity on $H_0$. It also records the
`01/122/201`, `12/012/221` and `12/120/221` controls and a probe of the 492
unit specimens with $\beta_1(E)\ge2$.

The census below is a brute-force maximum over invariant subgraphs on all
2628 unit specimens, and it is an independent check of that envelope. On
the $\beta_1\ge2$ subset it gives the same counts: 24 specimens with
$U_+>0$, and 12 with $\det M=-1$ and $U_->0$. The other 60 members with
$\det M=-1$ and a positive ceiling at $-1$ have $\beta_1\le1$. Barge's
Theorem 22 already excludes those at unit rank two.

New here relative to #604:
- Lemma B (the endpoint branch carries no seam term);
- its executable telescoping check;
- the Lean layer.

## Targeted literature stop/go check

The target is the obligation left by the
[seam-spectrum note](c4-one-track-seam-spectrum-2026-11-17.md) and the
[literal replay](c4-literal-seam-replay-2026-11-17.md)
(#602, merged through #604): bound the corrected odd multiplicity at
$\varepsilon=(\det M)^m$ below the rank of a neutral first-defect image.
This note imports no new external theorem. It uses only statements
already gated for #598 and #601:

| Source | Used for | Gate |
| --- | --- | --- |
| [Barge–Diamond, Theorem 4 and the eventual range](https://arxiv.org/pdf/math/0702669) | cyclic legal bigrams and the endpoint maps on them | [#601 gate](c4-one-track-seam-spectrum-literature-2026-11-17.md) |
| [Baker–Barge–Kwapisz, §§2–4](https://www.numdam.org/article/AIF_2006__56_7_2213_0.pdf) | unit normalization, common fibres, integral offsets | [#598 gate](c4-periodic-overlap-returns-literature-2026-11-17.md) |
| [Round 3, Proposition E (draft)](c4-round3-2026-11-16.md) | only to name the endpoint-coboundary form; its dichotomy is not used | repository draft, no verifier |

The sources were not re-read for this note. **Decision: proceed** with
written lemmas and source-only computations at the scope of those gates.

## Work shown

### Assumptions and hypotheses: what transfers to an actual strict component

Setting $\mathbf S$: $\sigma\in\mathrm{PIP}_3$, $|\det M|=1$, coincidence rank
two, and a strict system exists. The chain from literal data to the neutral
requirement is:

| Step | Statement | Source | Status |
| --- | --- | --- | --- |
| T1 | $Z$, bigon alphabet $B$, primitive swap-invariant $\Sigma$ with matrix $N$ | [Theorem W](c4-rank-two-wall-2026-11-16.md) | written, under $\mathbf S$ |
| T2 | the overlaps of $Z$ form the unique aligned nonproductive sink $C$ of the complete box | [#598](c4-periodic-overlap-returns-2026-11-17.md) | written, under $\mathbf S$ |
| T3 | $m_{N^-}(\zeta)=m_{A_C^-}(\zeta)+b_d$ for a primitive $d$-th root $\zeta$ | #598 trace identities and [#601](c4-one-track-seam-spectrum-2026-11-17.md) cycle theorem | written, under $\mathbf S$ |
| T4 | top-only seam graph $S$ of $C$ embeds equivariantly in copies of the cyclic bigram graph $E$ over the periodic interior states $I$; every cyclic germ lies on a cyclic edge | #601 | written, under $\mathbf S$ |
| T5 | a first defect $D_r$ of weight $(m,m,m)$ with $D_rN=\varepsilon D_r$, $D_rJ=-D_r$ forces $g_{N^-}(\varepsilon)\ge\operatorname{rank}D_r$ | #598, last paragraph; rows of $D_r$ are odd left $\varepsilon$-eigenvectors | elementary |
| T6 | $A_C\Pi=\Pi N$ and $J_C\Pi=\Pi J_B$, with $\Pi_{c,b}$ the number of cells of type $c$ in bigon $b$ | below | written, under $\mathbf S$ |

T6 holds because bigon cuts are shared: every cell of $Z$ lies in one
bigon, and the cells of $\Sigma(b)$ are exactly the children of the cells
of $b$. What does **not** transfer: every value computed on a productive
full box (the #601 table, the #602 replay, the census below) belongs to a
graph that is not a strict carrier. A strict carrier sees an invariant
subgraph of the copied graph, whose correction can be larger or smaller
than the full-box value. Lemma A below bounds that subgraph.

### Lemma A (source seam ceiling)

For an interior $f$-cycle $\gamma$ of period $p$, let
$\psi_\gamma=(g_R\times g_L)^p$ act on $E$. For a $\psi_\gamma$-invariant
edge set $E'$, let $V'_L,V'_R$ be its left and right letters. Put
$$
w_d(E',p)=\#\{\text{orbits of }E',\ d\mid p\,|O|\}
-\#\{\text{orbits of }V'_L\text{ under }g_R^p,\ d\mid p\,|O|\}
-\#\{\text{orbits of }V'_R\text{ under }g_L^p,\ d\mid p\,|O|\},
$$
and
$$
B_d(\sigma)=\sum_\gamma\max_{E'}w_d(E',p_\gamma),\qquad
F_d(\sigma)=\sum_\gamma\min_{E'}w_d(E',p_\gamma),
$$
with $E'=\varnothing$ allowed. Under $\mathbf S$,
$F_d(\sigma)\le b_d\le B_d(\sigma)$. Hence
$$
g_{N^-}(\varepsilon)\le m_{A_C^-}(\varepsilon)+B_{d}(\sigma),\qquad d=\operatorname{ord}\varepsilon .
$$
In particular $B_d(\sigma)=0$ gives $m_{N^-}(\zeta)\le m_{A_C^-}(\zeta)$
for every strict carrier of $\sigma$.

*Proof.* Under T4 a seam carries the interior state of the other track, so
$S$ is a disjoint union over the $f$-cycles. The block over $\gamma$ is the
union over its $p$ states of copies of an invariant subgraph $S_\gamma$ of
$E$, permuted cyclically. A $\psi_\gamma$-orbit of length $k$ in the base
copy is an orbit of length $pk$ of the whole map. The vertices of the block
are the endpoints of its edges by the last clause of T4. The cycle theorem
of #601 counts orbits whose length is divisible by $d$, which is
$w_d(S_\gamma,p)$ on the block. Each summand lies between the minimum and
maximum over invariant edge sets. $\square$

`kernel/psc/seam_correction_ceiling.mojo` computes $B_d$, $F_d$ and the
whole-copy value $W_d=\sum_\gamma w_d(E,p_\gamma)$ for $d\le4$. It uses the
certified complete $f$-cycle list of
[(F)](c4-geometric-f-class-2026-11-16.md) and refuses nonunit input.
$W_d$ is what the complete box realizes. The regression checks $W_d$ in two
further ways. One is Möbius inversion of fixed-edge minus fixed-germ counts
at powers $1$–$60$, without orbit weights. The other is #601's literal
full-box seam scanner.

### Negative control: positive literal correction at $+1$ with $\det M=+1$

The intermediate inequality *"$b_1\le0$, so
$m_{N^-}(1)\le m_{A_C^-}(1)$"* is false on literal geometry. Take
`01/122/201`, with $\det M=+1$, so $\varepsilon=+1$ at every weight
$(m,m,m)$:

- $g_R:0\mapsto1,1\mapsto2,2\mapsto1$ has the cycle $\{1,2\}$, and $g_L$ is
  the identity;
- the cyclic legal bigrams are $\{1,2\}\times\{0,1,2\}$, which is $K_{2,3}$;
- $I$ is one interior $f$-cycle of period $4$, and $\psi=(g_R\times g_L)^4=\mathrm{id}$.

Per copy $H_1(K_{2,3})-H_0(K_{2,3})$ has rank $2-1$. Induced over the
$4$-cycle, this gives $+1$ at every fourth root of unity:
$(b_1,b_2,b_3,b_4)=(1,1,0,1)$. In edges, endpoint germs and cycles, the
seam cycles have length $4$: $6$ of them, against $2$ last-letter and $3$
first-letter germ cycles.

**Literal replays.** #601's full-box scanner gives $b_1=b_2=+1$. The
independent #602 literal-word constructor (head `cbb8c6c6`, now on `main`)
gives the fixed seam, last and first counts $24,8,12$ at $n=4,8$. It gives
$0,0,0$ at the other $n\le11$, and $n=12$ refuses at the word cap. So
$U-L-R=4\cdot[4\mid n]$, the virtual trace of $+1$ at each fourth root of
unity. The box has no aligned nonproductive sink, so this is a productive
control and not a strict system. It supplements the `01/12/021` control at
$-1$. Neither sign of the seam correction is controlled by literal
geometry alone.

### Lemma B (the endpoint-coboundary branch carries no seam term)

Say $D_r$ has **endpoint-coboundary form** if there are swap-odd
$P,Q$ on ordered letter pairs with
$D_r(u,v)=P(u_{\rm last},v_{\rm last})-Q(u_{\rm first},v_{\rm first})$ and:

- (EC1) $P(\text{pair ending at }x)=Q(\text{pair starting at }x)$ at every
  shared cut $x$ of every pair in $Z$;
- (EC2) $P\circ(g_R\times g_R)=\varepsilon P$ and
  $Q\circ(g_L\times g_L)=\varepsilon Q$ on pairs at shared cuts of $Z$.

This is branch (a) of the round-3 draft Proposition E. Here it is a
hypothesis, and the draft dichotomy is not used. On cells of $C$ define
$$
\tilde\kappa(c)=\varepsilon^{-k}P\bigl(\text{pair of }g_R^k c\bigr)
-\varepsilon^{-j}Q\bigl(\text{pair of }g_L^j c\bigr),
$$
with $k$, resp. $j$, least such that $g_R^kc$ has a shared right end, resp.
$g_L^jc$ a shared left end. A term is omitted when no such power exists.
Then
$$
D_r=\tilde\kappa\,\Pi,\qquad \tilde\kappa A_C=\varepsilon\tilde\kappa,\qquad
\tilde\kappa J_C=-\tilde\kappa .
$$
Consequently
$\operatorname{rank}D_r\le g_{A_C^-}(\varepsilon)\le m_{A_C^-}(\varepsilon)$,
with no seam correction. The rank is also at most the dimension, at most
$6$, of the space of admissible $(P,Q)$.

*Proof.* Whether a cell end is shared is intrinsic to the cell type,
because $\ell$ is injective. A shared end stays shared, and a one-track end
can become shared after inflation (*promotion*). Along last children the
right end of $c$ is the same point inflated, so the least $k$, and the pair
there, depend only on $c$.

*Column identity.* The children of $c$ partition $\Phi(c)$. Interior to
$\Phi(c)$ there are three kinds of boundary between consecutive children
$u_1,u_2$:

1. A shared cut $x$. It contributes $P(\text{ends at }x)-Q(\text{starts at }x)=0$ by (EC1).
2. A one-track seam promoted after $k\ge1$ steps. It contributes
   $\varepsilon^{-k}\bigl(P-Q\bigr)$ at the promoted cut $\beta^kz$, which is $0$ by (EC1).
   The promoted pair of cells is adjacent in $Z$ by the #601 saturation lemma.
3. A seam that is never promoted. It contributes nothing.

At the right end of $\Phi(c)$, if the right end of $c$ is shared, the last
child contributes $P(g_R\text{-pair})=\varepsilon P(\text{pair})$ by (EC2).
If it is promoted after $k\ge1$ steps, the last child contributes
$\varepsilon^{-(k-1)}P(\cdot)=\varepsilon\cdot\varepsilon^{-k}P(\cdot)$.
Otherwise it contributes $0$. The left end is the same with $Q$. Summing,
$(\tilde\kappa A_C)(c)=\varepsilon\tilde\kappa(c)$.

*Factorization.* A bigon's first cell has the only shared left end and its
last cell the only shared right end, by irreducibility. Its interior seams
are one-track and cancel pairwise as in cases 2 and 3. So
$\tilde\kappa\Pi(u,v)=P(u_{\rm last},v_{\rm last})-Q(u_{\rm first},v_{\rm first})$.
Swap-oddness follows from that of $P$ and $Q$. The rows of $D_r$ are then
$\tilde\kappa$'s that are swap-odd left $\varepsilon$-eigenvectors of
$A_C$. $\square$

The promotion weights are necessary. The functional with only $k=j=0$ fails
the column identity on real columns, because every unit specimen without
(F) still has transient seams that get promoted.

**Executable control.** `kernel/psc/promoted_endpoint_functional.mojo`
checks the column identity symbolically in the six unknowns
$P(01),P(02),P(12),Q(01),Q(02),Q(12)$. The check runs on every column of a
complete literal box, at both signs. A residual must lie in the span of the
column's own (EC1) and (EC2) forms, and every promoted adjacency must be a
literal shared cut of the seam saturation. The table gives column counts and
failures per box, identical at both signs:

| Box | Columns | Promoted seams | $\tilde\kappa$ failures | naive failures |
| --- | --- | --- | --- | --- |
| `01/122/201` | 5784 | 4074 | 0 | 42 |
| `01/12/021` | 5014 | 5962 | 0 | 38 |
| `1/02/202` | 2832 | 916 | 0 | 22 |
| `1/2/021` | 1948 | 1316 | 0 | 16 |
| Tribonacci `01/02/0` | 740 | 484 | 0 | 20 |
| `12/021/122` | 1876 | 1652 | 0 | 40 |

An independent scratch Python oracle, not committed, gave the same counts.
This checks the telescoping algebra on literal rows. It does not produce a
nonzero admissible $(P,Q)$, which needs a strict carrier.

### Lean layer

[`proof/PscVerif/PscVerif/NeutralRankSeam.lean`](../proof/PscVerif/PscVerif/NeutralRankSeam.lean),
namespace `Psc.NeutralRankSeam`, has no `sorry`. Its audited theorems
depend only on `propext`, `Classical.choice` and `Quot.sound`.

| Statement | Lean | Scope |
| --- | --- | --- |
| $\kappa_R(g_Rc)=\varepsilon\,\kappa_R(c)$ | `promoted_comp` | from persistence and (EC2), $\varepsilon\ne0$ |
| adjacent cells: $\kappa_R(s)=\kappa_L(t)$ | `promoted_adj` | from closure under $(g_R,g_L)$, side agreement and (EC1) |
| $\kappa\circ J=-\kappa$ | `promoted_swap` | swap commuting with $g$, $P\circ J=-P$ |
| column identity | `EndpointData.column_identity` | a linked row from $g_Lc$ to $g_Rc$ |
| $\tilde\kappa A=\varepsilon\tilde\kappa$ | `vecMul_occ_eq` | $A$ the occurrence matrix of the rows |
| bigon sum | `EndpointData.bigon_sum` | a linked block with shared outer ends |
| $D=\tilde\kappa\Pi$ and $\operatorname{rank}D\le\dim$ odd $\varepsilon$-eigen-rows | `endpoint_rank_bound`, `rank_le_finrank_oddEigen` | Lemma B, abstract form |
| promotion weights are needed | `naive_fails` | three-cell model |
| `01/122/201`: $\det M=1$, endpoint maps, six legal bigrams fixed by $(g_R\times g_L)^2$ | `seam_det`, `seam_endpoint_maps`, `seam_bigram_legal`, `seam_bigram_cyclic` | `decide` on words and matrices |
| four interior addresses of period $4$ | `seam_isInteriorAddress_1`–`_4` | `Psc.GeometricFLemmas.IsInteriorAddress` |
| $U(n)-L(n)-R(n)=4\cdot[4\mid n]$, $n\le12$ | `seam_trace` | bigrams copied over a $4$-cycle |

A second round formalizes the items the first left open, as far as they
are statements with known proofs.

| Statement | Lean | Scope |
| --- | --- | --- |
| T6: $A\Pi=\Pi N$ | `NeutralRankSeam.occ_mul_occ` | from the literal flattening: an inflated block's cells are its cells' children and its child blocks' cells |
| E1 of Proposition E: the endpoint form gives $DN=\varepsilon D$ | `NeutralRankSeam.endpoint_defect_eigen`, `defect_eigen` | the direction used by Lemma B |
| spectral step of the #601 cycle theorem | `SeamCycleSpectrum.cycle_correction`, `mult_eq_card_order` | if the power sums of two multiplicities on the $D$-th roots of unity differ by the cycle counts $U-L-R$, they differ at a root of order $d$ by $\#\{q\in U:d\mid q\}-\#\{q\in L:d\mid q\}-\#\{q\in R:d\mid q\}$ |
| power sums determine multiplicities | `SeamCycleSpectrum.eq_of_vtrace` | injectivity of `ZMod.dft` |
| $\sum_{qk=0}\chi(kn)=q\,[q\mid n]$ | `SeamCycleSpectrum.sum_kernel` | $q\mid D$ |
| Lemma A, orbit law: $\operatorname{per}(e,i)=p\cdot\operatorname{per}_{\psi}(e)$ | `SeamCycleSpectrum.minimalPeriod_shift`, `isPeriodicPt_shift_iff` | $\psi=\pi^p$ on the base copy |
| Lemma A, ceiling and floor | `SeamCycleSpectrum.ceiling_bounds` | per-cycle admissible subgraphs |
| `01/122/201`: $\chi_M=X^3-3X^2+X-1$ irreducible, $M$ primitive | `NeutralRankSeamCycle.seam_charpoly`, `seam_irreducible`, `seam_prim` | |
| every interior address at $k\le4$ is one of the four, at $k=4$ | `NeutralRankSeamCycle.seam_address_classify` | enumerates occurrences in $\sigma^k(e)$ and the integrality of $\operatorname{adj}(M^k-I)\,p(P)/\det(M^k-I)$ |
| periodic interior states of period dividing $k\le4$ | `NeutralRankSeamCycle.seam_periodic_iff` | for every positive left eigen-row |
| the four states are $f^jx_0$, $j<4$: **one $f$-cycle** of exact period $4$ | `NeutralRankSeamCycle.seam_single_cycle` | for every positive left eigen-row |

Still not formalized, with the reason for each:

- **The transfer of a strict rank-two component to the `EndpointData` and
  T6 hypotheses** (T1–T5). This is the strict joining $Z$ of Theorem W,
  the BBK geometric realization, and the identification of $C$ with the
  overlaps of $Z$. It rests on tiling-space theory that the library does
  not contain. Inside the formal layer these facts are hypotheses: the
  fields of `EndpointData` and the flattening hypothesis of `occ_mul_occ`.
- **The endpoint-coboundary form itself.** Its source is the round-3 draft
  Proposition E, which has no verifier and whose proof is not known to be
  correct. Only its consequence E1 is formalized.
- **The trace identities of #598 and agreement of spectra away from roots
  of unity.** These are the hypothesis of `cycle_correction`. They depend
  on the same geometric transfer.
- **That $I$ has no states of period other than $4$.** Periods dividing
  $1$–$4$ are exhausted in Lean. Larger periods are excluded only by the
  certified Mojo search box of the (F) note, which is not formalized.

### Consequence for the obligation

Combining T3, T5 and Lemmas A and B:

- **Endpoint-coboundary $D_r$:**
  $\operatorname{rank}D_r\le g_{A_C^-}(\varepsilon)$. Positive seam
  corrections, at $-1$ for `01/12/021` or at $+1$ for `01/122/201`, cannot
  supply the rank. The obligation is a statement about the literal sink
  alone: no nonzero admissible $(P,Q)$ on $C$. By (EC1) the common value
  $H=P=Q$ is constant on each component of the bipartite shared-cut germ
  graph of $Z$ (left pairs, right pairs, an edge per shared-cut germ). The
  swap sends a component with value $H$ to one with value $-H$. So
  $H\equiv0$, and hence $D_r=0$, whenever the swap fixes every component,
  in particular when the graph is connected. Branch (a) therefore needs
  components exchanged by the swap.
- **Any other $D_r$:**
  $\operatorname{rank}D_r\le g_{A_C^-}(\varepsilon)+B_d(\sigma)$, and only
  here does the seam ceiling enter.

### Evidence and replay

```sh
cd kernel
pixi run --locked mojo run -I . -I tests tests/test_seam_correction_ceiling.mojo
pixi run --locked mojo run -I . -I tests tests/test_promoted_endpoint_functional.mojo
pixi run --locked mojo run -I . seam_ceiling_census.mojo
```

**Census of the source ceiling** over the 2628 unit corpus members
($\det M=+1$: 1980; $-1$: 648). 1200 have interior $f$-cycles; the others
satisfy (F), so all their values are $0$. Entries give
(ceiling $B_d$, whole copy $W_d$): count, over all members of that sign.

| $\det M$ | order | distribution |
| --- | --- | --- |
| $+1$ | $1$ (the only $\varepsilon$) | $(0,-2)$: 12, $(0,-1)$: 516, $(0,0)$: 1440, $(1,1)$: 12 |
| $-1$ | $1$ | $(0,-3)$: 24, $(0,-2)$: 228, $(0,-1)$: 228, $(0,0)$: 156, $(1,0)$: 12 |
| $-1$ | $2$ | $(0,-2)$: 108, $(0,-1)$: 180, $(0,0)$: 288, $(1,1)$: 48, $(2,2)$: 24 |

96 members have a positive ceiling at an order relevant to their
determinant: 12 with $\det=+1$ at order 1, and 84 with $\det=-1$. The corpus
maxima are $B_1=1$ and $B_2=2$. For 12 members of `12/120/221` type,
$B_1=1>W_1=0$: an invariant subgraph would do better than the full box. A
scratch run of #601's full-box scanner on all 252 members with a positive
ceiling at order 1 or 2 found the literal $(b_1,b_2)$ equal to
$(W_1,W_2)$ in every case. The corpus has no strict system, so these
counts map source configurations only. They are not evidence about strict
carriers.

### Tests executed

All runs were local with the repository-pinned Mojo toolchain. Hosted CI
has not run.

- `tests/test_seam_correction_ceiling.mojo`: pass. It pins 7 specimens,
  checks Möbius-inverted traces and literal full-box agreement, and checks
  the nonunit refusal.
- `tests/test_promoted_endpoint_functional.mojo`: pass. It covers 6 boxes,
  both signs, the naive negative control and the bad-$\varepsilon$ refusal.
- `tests/test_one_track_seam_spectrum.mojo` (existing): pass.
- `seam_ceiling_census.mojo`: complete over the corpus. The table above is
  its output; the log is in
  [the evidence packet](../evidence/seam-ceiling-2026-11-18/README.md).
- The #602 constructor on `01/122/201` at powers 1–12 was run from its
  PR head `cbb8c6c6`, before #604 brought it to `main`.
- `lake build` of `PscVerif.NeutralRankSeam`, `NeutralRankSeamCycle`
  and `SeamCycleSpectrum`: pass, with no warnings. An axiom
  audit was run on the main theorems. A full `lake build` of the library
  root also passes. The isolated `tools/check_lean.sh` was not run.

### Non-claims / remaining gaps

- No strict PIP3 component is constructed or excluded. Lemmas A and B are
  conditional on $\mathbf S$ and have had no independent review.
- Lemma B assumes the endpoint-coboundary form. Whether every neutral first
  defect has this form is exactly the round-3 draft dichotomy. That
  dichotomy has no verifier, and its other branch (a nonzero swap-odd
  class in $H^1(Z)$) is untouched here.
- The census and both literal controls are productive geometry. They refute
  sign laws on literal geometry. They say nothing about which subgraph a
  strict carrier would select.
- The 48 comparisons of #602 are not repeated or re-credited.

**Next necessary theorem.** Two literal statements, one per branch:

1. *(Endpoint branch.)* For an aligned nonproductive sink $C$ of a unit PIP3
   box, the admissible $(P,Q)$ space of (EC1) and (EC2) on the shared cuts
   of $C$ is zero. It suffices that the swap fixes every component of the
   shared-cut germ graph. This is a statement about shared cuts only. The
   positive seam controls do not bear on it.
2. *(Cohomological branch.)* Exclude a swap-odd $\varepsilon$-class in
   $H^1(Z;\mathbb Q)$, or bound $g_{A_C^-}(\varepsilon)+B_d(\sigma)$ below
   the rank. A possible route is to identify $H^1(Z)$ with $H^1(\Omega_\sigma)$
   when the first projection $Z\to\Omega_\sigma$ is injective. That would
   put the $\varepsilon$-part in $\tilde H^0$ of the source eventual range.
   It is not established here, and its injectivity hypothesis is not known
   at rank two in general.
