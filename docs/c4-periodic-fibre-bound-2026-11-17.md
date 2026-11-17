# Larger periodic fibres and return capacity at coincidence rank two

**Status:** Written proof conditional on the Baker–Barge–Kwapisz geometric
realization and coincidence rank two. The proof gives a quantitative
periodic fibre bound and a conditional return shortage. Exclusion of the
unit neutral-weight case remains open. Independent review and
formalization are pending.

[Literature check](c4-periodic-fibre-bound-literature-2026-11-17.md)

## Work shown

### Assumptions and hypotheses

Let $\sigma$ be a primitive irreducible ternary Pisot substitution with
$|\det M|=1$. Write $\Phi$ for inflation on the legal tiling space
$\Omega_\sigma$, $\beta>1$ for the expansion, and $\ell$ for the positive
length row with $\ell M=\beta\ell$. The two other eigenvalues of $M$ have
modulus less than one. The geometric realization is
$h:\Omega_\sigma\to\mathbb R^3/\mathbb Z^3$ with
$h\Phi=Mh$. We use the canonical strands. Their vertices have uniformly
bounded stable projections, and any vertex of a strand in the fibre
of $p$ has class $p$ modulo $\mathbb Z^3$. The full lattice is the
irreducible normalization of [BBK, §§2–3](https://www.numdam.org/article/AIF_2006__56_7_2213_0.pdf).

Assume coincidence rank two. Every legal fibre has two pairwise
noncoincident legal strands and no fibre has three. There is a
substitution-dependent uniform bound $K$ on full fibre cardinality.
Here noncoincident means that no common labelled edge appears at
any forward inflation. Nonerasure propagates a common edge to
every later inflation. [BBK, Definition 4.1 and Theorem 4.2](https://www.numdam.org/article/AIF_2006__56_7_2213_0.pdf)
· [Barge, Theorem 4](https://arxiv.org/pdf/1301.7094)

Write $F_n=\operatorname{Fix}(M^n)$ on the torus and set
$$
H_n=\#\{p\in F_n: \#h^{-1}(p)>2\}.
$$
The count $H_n$ includes all lifts of those base points, even lifts
permuted by $\Phi^n$.

### Derivation / reduction

**Theorem.** There is a finite matrix $L_3$ of literal triple overlap
occurrences, with $\rho(L_3)<\beta$, and a finite set $D$ of integral
displacements such that
$$
H_n\le 1+|D|\,\mathbf 1^\top L_3^n\mathbf 1 .
$$
In particular, $H_n=O(\gamma^n)$ for every
$\max(1,\rho(L_3))<\gamma<\beta$. The term $1$ accounts for the zero
base point.

**The finite graph.** Let $P_s$ be the stable projection and choose a
norm on its plane in which $M$ has operator norm at most $\rho<1$.
Write $D_s$ for the largest stable norm of a difference of two
proper image prefix columns. Take a radius $R$ at least $D_s/(1-\rho)$
and at least twice the bound on all strand vertex stable norms.
A state is a triple of labelled tiles with lattice starts
$0,z_2,z_3$, with $\|P_s z_i\|\le R$ and with a common interval of positive
physical length. Require the three labelled starts to be pairwise
distinct. The positive intersection bounds $|\ell z_i|$ by the
maximum letter length $W$. Thus the integral shift set
$$
D=\{z\in\mathbb Z^3:\|P_s z\|\le R,\ |\ell z|\le W\}
$$
is finite. The three labels and the two shifts specify a state.

An edge records one image digit on each of the three tracks whose
intervals have a positive common intersection after inflation.
If their integral starts are $Mz_i+p_i$, where $p_i$ are the chosen
proper prefix columns and $z_1=0$, rebase by the new first start $p_1$.
The radius bound persists by contraction and the choice of $R$.
Keep the edge exactly when the new labelled starts are pairwise
distinct. The matrix $L_3$ has parent columns and child rows. It keeps
different positional triples with multiplicity, including those
with the same rebased child state.

Write $w(s)>0$ for the width of the common interval of a state.
All positional children before the distinctness filter partition
the inflated common interval, up to endpoints. At each depth a
positive-width descendant triple has a unique ancestor on each
track. Its positive common interval lies inside the inflated common
interval of those ancestors, so no earlier tuple with zero common
width can conceal a later positive-width cell. Hence
$w^\top L_3\le\beta w^\top$. No positive-width child is lost at the
radius cutoff, so any strict inequality comes from a pair agreement.

**Why full growth would give three noncoincident legal strands.**
Suppose an irreducible block $C$ has spectral radius $\beta$. Multiply
the restricted width inequality by a positive right Perron vector of
that block. Equality in the sum forces equality in every parent
column. Every literal positive-width triple child of $C$ stays in
$C$ and has no pair agreement.

Choose $m$ so large that the width of every $m$-fold inflated common
interval in $C$ exceeds $2W$. Each such interval has a literal triple
child with nonempty portions of the interval on its left and right.
Indeed every child has width at most $W$, and the first and last cells
can account for at most $2W$. Choose one interior child per state and
take a cycle of these choices. After some $k\ge1$ levels the composite
occurrence returns to its original rebased state and is interior. A
proper interior occurrence remains interior under further expansion
inside its parent cell.

Let $J$ be the original common physical interval and $q$ the
composite prefix column of track one. The repeated triple interval is
$\ell q+J\subset\operatorname{int}(\beta^kJ)$. Place the first tile at
$x=-(M^k-I)^{-1}q$ and the others at $x+z_i$. The exact child
translations from all three paths now fix these three based tiles.
The displayed strict inclusion implies that zero is interior to
their common interval after this placement. Each seed tile is
contained in its own inflation by $\sigma^k$. The increasing legal
patches exhaust the line in each track. These periodic strands have
the same torus coordinate because their starts differ integrally.
The canonical lattice positions agree with this construction since
the repeated literal marks determine the starts uniquely by
$M^k-I$.

The expanding common intervals exhaust the line. A shared labelled
edge for any two limiting strands, at any forward level, would
persist to a multiple of $k$. It would then occur in a sufficiently
large common interval of the three expansions. An interior part
of that edge meets a tile of the third track in positive width,
giving a forbidden triple child with a pair agreement. The three
strands are therefore pairwise noncoincident, contrary to rank
two. Every irreducible block of $L_3$ has radius strictly less than
$\beta$.

**Coding an entire larger periodic fibre.** Let $p\in F_n$ with $p\ne0$.
The map $\Phi^n$ permutes its finite fibre. All its tilings are
individually periodic under some common power $\Phi^{n a}$. The same
holds at every intermediate fibre over $M^j p$.

A periodic tiling can have a vertex at the origin only in the zero
fibre. In fact inflation preserves a vertex at the real origin, and
periodicity would give a fixed lattice vertex $v=M^{n a}v$. Since
$M^{n a}-I$ is nonsingular, $v=0$. For a nonzero periodic base point
each lift has an interior centre tile at every intermediate level.
If two such lifts had the same centre tile with the same lattice
start, its nested inflations by their common period would determine
both complete strands and make them equal. Relative to the start of
any one lift, every other lift has a label and displacement in
$\{0,1,2\}\times D$. Thus a nonzero periodic fibre has at most
$3|D|$ elements, irrespective of its period and permutation.

Choose any ordered triple of distinct lifts of $p$. The three centre
tiles therefore give an $n$-edge path in $L_3$. Each edge retains the
digit of track one inside its preceding tile. Let $q$ be the
composite prefix column of that path and $v$ the original first
centre-tile start. Its image centre-tile start after $n$ steps is
$M^n v+q$. It belongs to a lift in the original fibre, so its
difference $d$ from $v$ lies in $D$. Crucially, the terminal tiling
may be a different lift and need not be one of the three selected
ones. The relation
$$
(M^n-I)v=d-q
$$
still recovers $v$ uniquely from the path and the single bounded
return displacement. The path and $d$ determine $p=v\bmod\mathbb Z^3$.
This bounds the number of nonzero exceptional base points by
$|D|$ times the number of occurrence paths. Finite-matrix growth
gives the claimed estimate.

There is also a finite width certificate for the strict rate.
When $L_3$ is nonempty, every state can reach a lost positive-width
child since the matrix has no full-width sink. With $m$ larger than
the maximal length of a shortest path to such a loss, every column
of $w^\top L_3^m$ is strictly smaller than $\beta^m w^\top$. The
largest ratio of these columns gives an explicit block contraction.
The empty graph has zero nonzero-fibre count.

**What happens to the pair supply.** A nonzero base point with
exactly two legal lifts has a noncoincident pair. The action of
$\Phi^n$ either fixes both lifts or transposes them. In the first
case each gives a distinct interior address $(a,i)$ in
$\sigma^n(a)=P\,a\,Q$. Its torus class is
$-(M^n-I)^{-1}p(P)$ modulo the lattice. Consequently equality of
classes is exactly equality of the prefix residues modulo
$(M^n-I)\mathbb Z^3$. The transposed case gives no ordinary fixed
address pair at that power.

Let $s_n$ count the two-lift fibres away from zero on which both
lifts are fixed, and $u_n$ count those on which they are exchanged.
If $f_n=\#\operatorname{Fix}(\Phi^n)$, then
$$
2s_n=f_n+O(K(H_n+1)),
\qquad
s_n+u_n=\# F_n+O(H_n+1).
$$
The fixed-point formula counts interior letter occurrences by
$\operatorname{tr}(M^n)$ with bounded first, last and legal seam
corrections. Thus $f_n=\beta^n+O(1)$. Also
$\# F_n=|\det(M^n-I)|=\beta^n+O(\eta^n)$ for some $\eta<\beta$,
by the contracting eigenvalues. Both $2s_n$ and $2u_n$ have leading
term $\beta^n$ with an error of strictly smaller exponential rate.
[Fixed-point formula](c4-rank-two-wall-2026-11-16.md)

Let $A_n$ count ordered ordinary fixed address pairs in the same
residue that remain noncoincident and have an interior address on
at least one track. This is the count before the bounded-gap test
on common vertices. The nonzero two-lift fibres contribute exactly
$2s_n$. The remaining contribution is at most $K(K-1)(H_n+1)$.
In particular $A_n=\beta^n+O(\gamma^n)$ with the rate from the
periodic fibre bound. This excludes a leading-order shortage from
the fibre-size estimate alone.

**Conditional return shortage.** Suppose a strict component is
given in the rank-two sector. Theorem W gives its primitive ordered
bigon system $B$ for $\sigma$ and puts both orders of every two-lift
fibre in that component. At a nonzero split fibre the origin cannot
be a common vertex. Consecutive common vertices around the origin
therefore pick out an interior bigon. Inflation fixes the ordered
pair, so that bigon occurs inside its own $n$-th row. Conversely
an interior self-factor defines a unique ordered fixed pair by
iterating its two patches about the centre. This is an injection
because the addresses recover the two bounding common vertices
and the start index. Thus all $2s_n$ ordinary pairs from nonzero
two-lift fibres are consumed by the component, if it exists.
[Rank-two component and uniqueness](c4-rank-two-wall-2026-11-16.md)

With child matrix $N$, the number $R_n$ of interior returns satisfies
$$
\operatorname{tr}(N^n)-2|B|\le R_n\le A_n,
\qquad
0\le A_n-R_n\le K(K-1)(H_n+1).
$$
The first inequality excludes at most the first and last occurrences
per row. Restricting $A_n$ to pairs with bounded common-vertex gaps
preserves these inequalities. Under the strict-component hypothesis
the possible slack is confined to the exceptional contribution.

One sufficient spectral obstruction is precise. Let $P$ be the
Parikh map from the bigon alphabet and suppose the proposed child
matrix respects $PN=MP$. Irreducibility and a nonzero Parikh column
give surjectivity. If
$$
\rho(N|_{\ker P})>\max(1,\rho(L_3)),
$$
there are arbitrarily large $n$ for which
$\operatorname{tr}(N^n)-2|B|>A_n$. In fact the trace difference
$\operatorname{tr}(N^n)-\operatorname{tr}(M^n)$ is the power sum on
$\ker P$. Along an unbounded subsequence the phases of all eigenvalues
of its greatest modulus approach 1 simultaneously. This follows by
recurrence of powers of their tuple in a compact torus. The positive
power sum on that subsequence grows at the greater rate, while
$A_n=\operatorname{tr}(M^n)+O(\gamma^n)$ for each rate allowed above.
The neutral eigenvalue $\pm1$ from a unit $(m,m,m)$ defect does not
supply this strict inequality.

### Evidence and replay

The proof uses the merged baseline `0c1bdb52ad7b24562fadd9eb150845704e472d4b`
and has no finite sample premise. The relevant finite object is the
complete triple occurrence graph, with its stable radius, word digits
and widths as specified above. The proof bounds the **full** periodic
fibre count through paths with a bounded return displacement. A test
that requires the three lifts to return individually at power $n$ would
verify only the smaller fixed-lift count. The new graph and inequality
have a written proof and await executable certification. The two
literal controls below replay with the pinned Mojo compiler.

```sh
cd kernel
pixi run --locked mojo run -I . -I tests tests/test_periodic_fibre_controls.mojo
```

The regression enumerates every interior occurrence in the named
powers and tests the exact torsion class using integral arithmetic.
It cross-checks the zero-fibre classifications using the existing
zero-fibre routine. The 1,024-letter image cap is inconclusive if
reached.

### Negative controls

| Unit PIP control | Torus class | Verified fixed lifts |
| --- | --- | --- |
| `1/2/021` | $(1,0,1)/2$ | Four at power three, at digit 3 for letter 1 and digits 3, 5 and 7 for letter 2 |
| `01/12/021` | $(17,4,7)/19$ | One at power three and five at power six. The other four of these five lifts form two transpositions under the third inflation. |

Both controls pass the rank-one zero-fibre comparisons. The second
control verifies why a path which ends at a different lift must count
toward a bound on full fibres.

**A unit two-sheet control.** For the round-three incidence matrix of
`1/2/021`, its column sums are all odd. Put
$L=\{v\in\mathbb Z^3:\sum_i v_i\equiv0\pmod2\}$.
The matrix preserves $L$ and induces a two-to-one toral covering
$\mathbb R^3/L\to\mathbb R^3/\mathbb Z^3$ commuting with inflation.
For a base fixed point represented by $x$, the action on its two lifts
is determined by the parity of $(M^n-I)x$. The map from
$\mathbb Z^3/(M^n-I)\mathbb Z^3$ to $\mathbb Z/2$ given by this parity
is well-defined and surjective. Exactly half the periodic base
points fix both lifts and half exchange them, at every $n$. The
quotient has no larger fibres and its ordinary ordered pair count is
$|\det(M^n-I)|$. This is a control for the cardinality inference on
a genuine unit dynamical cover. Its domain is a torus. The literal
tiling of `1/2/021` has a different period-two address count.

### Non-claims / remaining gaps

The unit neutral-weight sector requires a new bound after the
bounded-gap and literal common-cut constraints are imposed, or
a separate contradiction to their realization. In particular, a
single nonzero split two-lift fibre with unbounded common-vertex
gaps would contradict the strict-component hypothesis by Theorem W.
A full fibre-size bound and its subleading error leave the leading
return demand and the leading supply equal. The sufficient spectral comparison
above leaves the neutral case open. No conclusion on universal C4
or PSC follows from this increment.
