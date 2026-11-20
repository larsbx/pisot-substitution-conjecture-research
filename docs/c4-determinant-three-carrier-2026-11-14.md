# Termination with coincidence for the determinant-three family

**Status:** exact symbolic and finite replay. Independent human review pending.

This continues [issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461).
The [source review](c4-determinant-three-carrier-stop-go-2026-11-14.md) records the hypotheses of the spectral criterion.

**Theorem.** For every integer $k\ge 3$, the balanced-pair algorithm for
$(01,10)$ under $\sigma_k=(1,01^k2,0001)$ terminates with coincidence.
Every irreducible factor of every iterate reaches a singleton coincidence
within two more substitutions. For $k\ge 4$ one more substitution suffices.
The substitution tiling flow of every $\sigma_k$ has pure discrete spectrum.

## The unbounded range

Write $A=01^k2$. The certificate in
[test_c4_determinant_three_carrier.mojo](../kernel/tests/test_c4_determinant_three_carrier.mojo)
gives 29 pairs for $k\ge9$, including $01/10$ and the singleton pairs
$0/0$ and $1/1$. Its row for each noncoincident pair lists every child
occurrence in order, with track orientation and multiplicity. The row
for $01/10$, for example, is $10/01$, followed by $k-1$ copies of $1/1$,
then $12/21$. Both tracks reconstruct the respective literal images
$1A$ and $A1$.

The [checker](../kernel/psc/c4_affine_carrier.mojo) verifies the rows
with these finite word identities, uniformly over $n=k-9\ge0$.

1. Write each word as runs of constant letters with lengths $an+b$.
   The alignment of two tracks advances by the smaller residual run
   length, as certified by coefficientwise nonnegativity. For each such
   alignment interval with equal letters, the prefix Parikh difference
   is constant. Intervals with unequal letters have constant length
   in this table and are checked position by position. Every proper
   nonempty prefix has a difference coordinate with fixed strict sign
   on $n\ge0$. At the end the difference is zero and both tracks have
   ended. Thus every listed pair is irreducible, with the singleton
   coincidences immediate.
2. On each track, concatenate the listed occurrences and compare the
   result with the corresponding image of the parent. Compute the
   parent image by $0\mapsto1$, $1\mapsto A$, $2\mapsto0001$. Both sides
   coalesce adjacent runs and contract an explicit substring
   $01^k2$ to the auxiliary symbol $A$. For every block repeated a
   parameter-dependent number $m$ of times, split the block as $XY$
   just before its unique $0$. The checker verifies the rotation
   $YX=A$ and replaces $(XY)^m$ by $X A^{m-1}Y$. All these rewrites
   preserve the word after replacing $A$ by $01^k2$. The checked
   equality of the resulting run lists therefore proves both literal
   concatenation identities for every $k\ge9$.
3. The verified child pieces are balanced and irreducible, so the
   two identities give the complete row cut at every Parikh equality.
   Each noncoincident row contains a singleton coincidence. Swapping
   the two parent tracks swaps every child in its row, without
   changing the order of the cuts. Complete the finite carrier by
   adding all swaps and the singleton $2/2$. Any diagonal inflates
   into a word of singleton diagonals. Thus there are at most
   $2\cdot27+3=57$ ordered states, and every noncoincident member
   has a diagonal child.

All cuts between factors survive inflation because an equal pair of
prefix Parikh vectors remains equal under the incidence matrix.
Consequently, by induction the consecutive-cut factors of
$(\sigma_k^j(01),\sigma_k^j(10))$ are precisely the successive child
occurrences from the seed. The carrier bounds the union of these
factors over all depths. The coefficient proof uses no cutoff on $k$
or depth.

## Finite boundary

For $3\le k\le 8$, use the canonical ordered occurrence graph from
$01/10$, including all diagonals and their children. Breadth-first
exploration must finish below the three refusal limits
(1,200 states, 100,000 child occurrences and 100,000 letters per
one-step track). Reverse propagation from the singleton coincidences
then gives the shortest distance for every attained state.

| $k$ | Ordered states | Child occurrences | Longest factor | Maximum coincidence distance |
| --- | ---: | ---: | ---: | ---: |
| 3 | 587 | 66,538 | 9,531 | 2 |
| 4 | 243 | 10,983 | 264 | 1 |
| 5 | 65 | 1,636 | 44 | 1 |
| 6 | 57 | 2,171 | 49 | 1 |
| 7 | 57 | 3,136 | 54 | 1 |
| 8 | 57 | 4,293 | 59 | 1 |

The replay also checks literal closures at $k=9,16$. The separate
Python replay cuts literal words using prefix counts. It checks the
ordered graph counts, the maximum distances and every symbolic-row
occurrence at $k=8,9,10,16,31$. Flipping the seed row's first child's
orientation, omitting a diagonal occurrence, or reordering the row
breaks the symbolic concatenation. A state budget of ten refuses
completion at $k=3$.

## Spectral consequence

The incidence matrix has a positive square, determinant 3 and
characteristic polynomial $f(X)=X^3-kX^2-2X-3$. Its unique positive
root $\beta$ lies strictly between $k$ and $k+1$, by opposite signs and
monotonicity of $x-k-2/x-3/x^2$ for $x>0$. For $t\ge0$,
$f(-t)=-t^3-kt^2+2t-3\le1/k-3<0$. Thus the cubic has no integer
root and is irreducible. The other roots are complex conjugates
of squared modulus $3/\beta<1$. This proves the primitive
irreducible Pisot hypotheses for $k\ge3$.

The finite carrier and its coincidence distances establish
termination with coincidence in the sense of
[Barge–Štimac–Williams, Theorem 3.2 and Corollary 2](https://doi.org/10.3934/dcds.2013.33.579).
Their criterion for the single swap of distinct letters $0,1$ applies
and gives pure discrete spectrum for the tiling flow. The spectral
implication uses the published theorem.

## Replay and scope

```sh
cd kernel
pixi run --locked mojo run -I . tests/test_c4_determinant_three_carrier.mojo
cd ..
python -m pytest tests/test_c4_determinant_three_carrier_oracle.py
```

This proves the forward and spectral conclusions for determinant three
on this family. For $r>3$ in $(1,01^k2,0^r1)$ the earlier
[bilateral newborn exclusion](c4-bilateral-newborn-family-2026-11-14.md)
gives the strict-system result, and a finite forward carrier remains to
be proved. The general ternary conjecture and the general extraction of
a finite carrier from failure remain open. The new certificate runs in
Mojo and has an independent literal replay in Python.
