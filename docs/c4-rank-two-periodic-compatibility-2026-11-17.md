# Shared cuts and full periodic fibres at coincidence rank two

**Status:** Written reduction in the unimodular PIP3 setting. The finite
nonzero periodic-fibre catalogue and named controls are replayed in Mojo.
Independent review and Lean formalization are pending. The neutral-weight
sector of universal C4 remains open.

[Targeted literature check](c4-rank-two-periodic-compatibility-literature-2026-11-17.md)

## Work shown

### Assumptions and hypotheses

Use the legal tiling hull of a primitive irreducible ternary Pisot
substitution with unimodular incidence matrix $M$, inflation $\Phi$
and expansion $\beta>1$. Use the Baker–Barge–Kwapisz (BBK) normalization
$h:\Omega_\sigma\to\mathbb R^3/\mathbb Z^3$, $h\Phi=Mh$.
Canonical strand vertices have uniformly bounded stable projections.
Their coset modulo $\mathbb Z^3$ is the value of $h$.
The hull is compact and translation-minimal, and $\Phi$ is invertible
on it. Write $\ell M=\beta\ell$ for the positive length row and
$W=\max_a\ell(e_a)$. Irreducibility makes $\ell$ injective on rational
vectors. A *shared cut* is a common vertex on the real line.
A tiling pair is *noncoincident* if no common labelled tile appears at
any nonnegative inflation level. A strict system is a nonempty
finite set of legal irreducible balanced pairs whose two words
differ, closed under all literal balanced-pair factors of an
inflation power, in the sense of [Theorem W](c4-rank-two-wall-2026-11-16.md).
[BBK, §§2–4](https://www.numdam.org/article/AIF_2006__56_7_2213_0.pdf)

### Derivation / reduction

**Theorem (uniform shared cuts at rank two).** Assume coincidence rank
two. The following are equivalent.

1. A strict system exists.
2. Every closed interval of some fixed length $L$ meets a shared cut
   of every pair in a common legal fibre.
3. Some noncoincident pair in a common legal fibre has bounded
   shared-cut gaps.
4. Every state in the complete Proposition V box graph reaches a
   state with zero displacement.

If these conditions fail, there is a legal periodic same-fibre pair
with no shared cut. In particular, any same-fibre pair with arbitrarily
long cut-free intervals suffices to exclude a strict system, with no
restriction on its base class, period, full fibre size, or label
coincidences.

**Closedness of the geometric tests.** Starts of two tiles in a common
fibre differ by an integral column $z$. When $|\ell(z)|\le1$, the
uniform stable bound on the strands restricts $z$ to a finite set.
Injectivity of $\ell$ on integral columns gives a uniform positive
lower bound on the absolute value of a nonzero such displacement.
This separates unequal cuts across the two tracks. If same-fibre pairs
converge in the tiling topology and the limit has a shared cut, the
corresponding two cuts in the approximants approach one another and
therefore coincide eventually. If the common cut begins an equal
label on both tracks, the labels also agree in the approximants.
The fibre relation is closed by continuity of $h$. These observations
make both vertex-disjointness and noncoincidence closed relative to
this relation, the latter by applying the labelled-tile test at
each forward level. Having a shared cut in every closed interval of
length $L$ is also closed. For each interval, take a subsequence of
its witnessing cuts in the compact interval and use local tiling
convergence on both tracks.

**From a strict system to uniform gaps.** If condition 2 fails, take
same-fibre pairs with arbitrarily large cut-free intervals and translate
their midpoints to zero. A compact limit is a same-fibre pair with no
shared cut by the preceding separation argument. Its orbit closure
contains a compact minimal joining of vertex-disjoint pairs. There is
at most one compact minimal joining of distinct fibre-mates at rank
two. Indeed, the first projection of any such joining is the whole
minimal hull, and through a tiling in a two-element fibre the ordered
pair has a unique second entry. Two minimal joinings then share a
point and agree. A strict system gives such a joining, with shared
cuts between consecutive finite bigons, by Theorem W and its Lemma 8
input. It cannot agree with a joining of vertex-disjoint pairs. Thus
condition 1 implies condition 2.

**From a bounded-gap pair to literal factors.** Condition 2 implies
condition 3 because rank two supplies a noncoincident pair in every
legal fibre. Under condition 3 take a compact minimal joining in the
orbit closure of the given pair. Both its gap bound and
noncoincidence persist by closedness. Its image under
$\Phi\times\Phi$ is a compact minimal joining of distinct
fibre-mates, since inflation scales the flow and acts invertibly.
Uniqueness gives inflation invariance. Take all ordered blocks of
this joining between consecutive shared cuts. The two tracks have
the same physical length between the cuts, so injectivity of
$\ell$ on their integral prefix difference gives equal Parikh
columns. The intervening shared cuts are exactly the equal-Parikh
prefix cuts. Consecutive cuts thus give an irreducible balanced
pair, and every literal irreducible factor of its substituted
words is another such block in the joining. The bound on physical
width and the least prototile length bound the word lengths.
All words are legal and none of the blocks is coincident. This is
a finite strict system for $\sigma$ itself.
[Barge, Theorem 4](https://arxiv.org/pdf/1301.7094)

**The finite box.** The complete box in Proposition V actually
contains *every* overlap occurring in any same-fibre pair. To
see this, take an interior point of its positive-width interval and
follow its ancestors in $\Phi^{-k}T,\Phi^{-k}T'$. These remain
same-fibre pairs because $M$ is a torus automorphism. The point stays
interior to both ancestral tiles, since vertices inflate to vertices.
For each contracting embedding $\tau$, the backwards iterates
satisfy the same bounded stable-coordinate condition. Solving the
child recurrences $t_{j+1}=\beta t_j+c_j$ along the ancestors and
letting $k\to\infty$ gives
$$
|\tau(t_0)|\le \frac{\max_c|\tau(c)|}{1-|\tau(\beta)|}.
$$
Here $c$ ranges over the proper-prefix increments of Proposition V.
This is its cycle bound with a bounded backward orbit in place of a
periodic one. The same trace-dual estimate puts the integral
displacement in its start box.

If condition 4 holds, take $H$ to be the largest first alignment
depth in the *whole* box graph, transients included. In any same-fibre
pair, every overlap cell of its $H$-fold desubstitution therefore
has a shared cut in its inflated closure, since an earlier alignment
also persists to depth $H$. The cells tile the line up to endpoints.
Each has inflated length at most $\beta^H W$. Every closed interval
of length $2\beta^H W$ contains at least one of these inflated
cells and hence a shared cut. This proves condition 2. If condition
4 fails, all descendants of a state without an aligned descendant
also lack one. Proposition V and the converse of Theorem B extract
an interior periodic occurrence pair from this finite closed set.
Its offsets are integral, hence the pair belongs to one BBK fibre,
and it has no shared cut. This disproves condition 2 and proves the
periodic witness assertion.
[Proposition V](p1b-vertex-coincidence-box-2026-10-02.md) ·
[Lemma C and Theorem B](p1b-strict-zipper-periodic-pair-2026-10-02.md)

**Consequence for the return supply.** In the notation of the
[periodic-fibre bound](c4-periodic-fibre-bound-2026-11-17.md), define
$G_n$ by retaining from $A_n$ the ordered noncoincident fixed
address pairs with bounded shared-cut gaps. At rank two,
$G_n=A_n$ at every $n$ in the presence of a strict system,
including the contributions from exceptional fibres. In the
absence of a strict system, $G_n=0$ at every $n$ by condition 3.
Consequently an independently certified gap failure already
excludes the strict system. This filter cannot give a smaller positive
pair supply under the strict-system hypothesis. A return shortage
in the neutral case still needs an independent exclusion or a finer
literal condition than bounded gaps.

**Proposition (full fibre over a nonzero periodic class).** Let
$p=b/d\bmod\mathbb Z^3\ne0$, $d>0$, with $M^n p=p$. All lifts
of $p$, including those moved by $\Phi^n$, are in bijection with
cyclic states of the following finite first-return map.

Use centre-tile states $(a,v)$ with $v\in -p+\mathbb Z^3$ and
$0<\ell(v)<\ell(e_a)$, where the tile is based at $-v$. For
$\sigma(a)=U a' V$, choose the unique occurrence containing
$\beta\ell(v)$ and set $f(a,v)=(a',Mv-\pi(U))$. Record the
index of that occurrence. The coset evolves as $-M^j p$, which
stays nonzero by unimodularity. Injectivity of $\ell$ on rational
vectors precludes a state at a cut or a child seam.

Use the trace-dual stable bound of the prototile map. Its
contraction estimate applies to rational $v$. The routine
`stable_radii` returns the floors
$R_i$ of rational upper bounds for periodic coordinates, so
$|v_i|<R_i+1$ suffices as an outer bound for rational periodic
states. For $0\le b_i<d$ the values $v=k-b/d$ with
$-R_i\le k_i\le R_i+1$ include all such states. Enumerate those
integers, retain the interior states, and draw the edge $f^n$
when it ends at an enumerated state. The catalogue keeps exactly
the cyclic states. Each return edge stores the $n$ literal
one-step indices and the exact successor.

Indeed, $\Phi^n$ permutes the finite legal fibre of $p$.
Every lift therefore returns at a multiple of $n$ and has an
interior centre tile, since a periodic tiling at an origin seam
would have its origin vertex fixed by $M^k$ and hence equal to
zero. Reading the centre tile gives a state in a return cycle.
Conversely a cyclic state has $f^{nr}(a,v)=(a,v)$ for some
$r>0$. The recorded occurrences give the same based tile in its
own expansion by $\Phi^{nr}$. Its iterated legal inflations
are nested and exhaust the line on both sides of the interior
origin. They give a single legal periodic tiling. The bounded
stable realization agrees with the prescribed based starts,
which are uniquely determined by the return equation with
$M^{nr}-I$. The resulting torus coordinate is $p$.
Two distinct tilings cannot have the same centre state: inflating
that tile by their common period would recover both tilings.
Reading the state after inflation shows that the first-return
edges encode the action of $\Phi^n$ on the full fibre.
[Integral prototile map and bounds](c4-geometric-f-class-2026-11-16.md)

**Gap test for one periodic pair.** The two centre tiles in a
nonzero fibre give a positive-width overlap with integral
displacement. Use its complete literal overlap closure, with
equal-label diagonals terminal because they already align and
substitute identically. A reachable overlap with no aligned
descendant produces arbitrarily long cut-free intervals.
Inflate its interval farther, then use levels divisible by the
pair's common period. Any shared cut in the open interval would
be a left-aligned descendant. Conversely if every reachable
state aligns by depth $H$, enlarge the common centre patch
to a sufficiently large common multiple of the periods. Its
overlap cells $H$ levels earlier all have a shared cut after
those $H$ levels. The same $2\beta^H W$ bound applies on
every interval of the original pair. Thus an existential
root hit tests a single shared cut, while reachability of a
state unable to align tests failure of the gap bound. A
labelled-tile hit is a third test. Periodic expansion of the
centre patch exhausts the line, so absence of a labelled
descendant here is equivalent to noncoincidence.

### Evidence and replay

`kernel/psc/periodic_fibre.mojo` uses scaled integer numerators
and the existing exact Perron sign and prefix routines. The
return graph checks every candidate in the certified box.
The pair graph enumerates every positive-width child occurrence
and runs reverse reachability to identify all descendants
without an alignment path. The work cap counts lattice positions,
base-residue steps and candidate-return steps. The overlap
cap is independent. Caps and uncertified arithmetic raise
without returning a catalogue or gap verdict.

```sh
cd kernel
mojo run -I . -I tests tests/test_periodic_fibre_controls.mojo
```

For `1/2/021`, the fibre over $(1,0,1)/2$ has exactly four
lifts, all fixed by $\Phi^3$. All six unordered pairs have
bounded gaps and a labelled-tile coincidence. The all-states
alignment depth bound in their union of closures is five.
For `01/12/021`, the fibre over $(17,4,7)/19$ has exactly
five lifts. The action of $\Phi^3$ has cycle lengths $1,2,2$.
All ten unordered pairs have bounded gaps and a labelled-tile
coincidence, with all-states alignment depth bound four.
Tribonacci has three lifts over $(1,1,1)/2$. The action of
$\Phi$ is a three-cycle. All three unordered pairs have bounded
gaps and a labelled-tile coincidence, with alignment depth
bound three. Direct residue scans of the literal powers are
independent counts of the ordinary fixed marks. The replay also
checks each indexed return against the expanded word.

### Negative controls

The five-lift example has one ordinary fixed mark at $\Phi^3$.
Tribonacci has none at $\Phi$ in its three-lift fibre. In each of the two
named fibres an unequal-label pair shares a cut from depth zero
and first coincides as a labelled tile at depth four.
These are different predicates even on the productive controls.
The neutral abstract system from round three uses the incidence
data of `1/2/021`. Its large literal test fibre supplies no
noncoincident pair. The example tests the missing realization
step, since the abstract constraints alone give no legal tilings,
indexed source occurrences or cut-gap verdict.
[Round-three obstruction](c4-round3-2026-11-16.md)

The reducible unit strict control `1/012/101` fails the PIP
screen. The nonunit PIP control `1/012/001` fails the
unimodularity test. Invalid residues, wrong return powers and
both caps are refused. A literal unit PIP periodic pair with unbounded
gaps would already give a noncoincident pair and contradict
pure discreteness, so the controls contain no such example.

### Non-claims / remaining gaps

The uniform-gap lemma is conditional on rank two and the
geometric realization. The finite catalogue treats a specified
nonzero unit torus class within the kernel's audited substitution
range. The zero class retains its separate seam catalogue. No
rank-two PIP example, return shortage, or universal C4
proof is established. The neutral sector needs a way to force a
reachable overlap without an alignment path under the rank-two
hypotheses, or a finer obstruction based on literal irreducible
factor returns. The abstract countermodel's algebraic data alone
do not resolve either obligation.
