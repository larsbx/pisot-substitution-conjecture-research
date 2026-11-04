# Forward Pisot run family: exact minimum simultaneous left-coincidence generation — 2026-11-04

**Status and scope.** This is a family-specific *sharp-depth* refinement of merged
[#479](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/479)
and the historical positive-run [#477](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/477).
The result is a uniform algebraic argument over unbounded nonnegative
parameters, with a bounded native Mojo checker and an independent literal
Python oracle. It is **not** a theorem about the first coincidence of an
arbitrary balanced seed, nor a general C4/PSC/PDS result. It does not address
minimal left-coincidence levels for the separately proved reversed family
[#481](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/481).

## The precise optimization problem

Let a,b be integers >=0, s=a+b>=1 and

```text
sigma(0) = A = 01
sigma(1) = B = 1^a 2 1^b
sigma(2) = C = 012.
```

Define D(a,b) as the **least positive integer n** such that some
common *physical position* p in the three genuine complete words
sigma^n(0), sigma^n(1), sigma^n(2) has
(i) the **same Parikh vector Q** strictly before p in all three words,
and (ii) the **same next letter z** at p in all three words.
Equal Parikh vectors force equal length, so no unsynchronized
physical-index convention is being imposed.

The primitive irreducible Pisot spectrum, characteristic polynomial
`x²(x−2) − s(x−1)²`, and the exclusion of a=b=0 are already
proved in #479 and are not strengthened here. All splittings at fixed s
have **identical incidence**, not identical word order.

## The sharp-depth theorem

**Theorem (five mutually exclusive chambers).** For every a,b>=0,
a+b>=1, the following table gives exactly D(a,b), together with one
true simultaneous witness (p,Q,z).

| Parameter chamber | **D(a,b)** | p | Q=(#0,#1,#2) | z |
| --- | ---: | --- | --- | ---: |
| a=0, b>=1 | **2** | 0 | (0,0,0) | 0 |
| a=1, b>=1 | **2** | b+3 | (1,b+1,1) | 1 |
| a=1, b=0 | **3** | 7 | (2,3,2) | 1 |
| a>=2, b>=1 | **3** | a(s+1)+1 | (1,as,a) | 1 |
| a>=2, b=0 | **4** | a³+a²+4a+1 | (a+1,a³+2a,a(a+1)) | 1 |

The theorem proves *minimum generation*, not minimum index p
within that generation. Some pairs of source letters may coincide
earlier than the simultaneous all-three event: **D is not the maximum
of the independently optimized pairwise depths unless separately proved.**

In particular, the former #479 level-three witness at a=1,b>=1
is correct but **one generation late**. Its published p=s+2
happens to equal the new level-two p. The a=1,b=0 previously
exhibited level-four witness is correct but **one generation late**.
The original `verify_closed_run_coincidence` remains unchanged
to preserve its previously published certificate; the new
`verify_sharp_closed_run_coincidence` makes the improved claim.

### Positive witnesses

* **a=0.** Already in #479: sigma²(0)=AB, sigma²(1)=CB^b,
  sigma²(2)=ABC. Their first letters are 0.
* **a=1,b>=1.** Here B=`12 1^b`. The true second images are
  F=AB, G=BCB^b, H=ABC=FC. At `p=b+3`, F and H
  have prefix `0112 1^(b−1)`, while G has prefix `B0`.
  Both have mass `(1,b+1,1)` and are followed by 1.
  The nonnegative exponent b−1 is why b=0 is excluded.
* **a=1,b=0.** Set F=AB=`0112`, G=BC=`12012`,
  H=ABC=`0112012`. The *third* words are `FG`, `GH`,
  `FGH`. At `p=7`, their prefixes are respectively
  `0112120`, `1201201`, `0112120`, each of mass
  `(2,3,2)`, each followed by 1.
* **a>=2,b>=1.** The uniform level-three literal witness from
  merged #477/#479 gives p=a(s+1)+1, Q=(1,as,a), z=1.
* **a>=2,b=0.** The uniform fourth-level F/G/H word identity
  of #479 gives p=a³+a²+4a+1 and the listed Q,z.
  No bounded-parameter extrapolation is needed for either
  already established infinite-parameter identity.

### No earlier simultaneous witnesses

**Level one.** sigma(0) starts with 0; sigma(1) starts with
1 (a>=1) or 2 (a=0), while sigma(2) starts with 0.
Thus p=0 is impossible. The only other possible position of
sigma(0)=01 is p=1, but its prefix contains a zero and
no nonempty prefix of B contains a zero. Hence D>=2 always.

**Level two, a>=1.** The actual words are F=AB,
G=B^a C B^b, H=ABC. F is an initial segment of H.
F has exactly one zero, at position 0, and length s+3.
The first zero of G is at index `a(s+1)`.
Every candidate p>=1 in F needs that zero to have
*already occurred* in G, requiring
`p>=a(s+1)+1`; and p<=s+2.
For a>=2 this is impossible: a(s+1)>s+1.
For a=1 the only possible index is `p=s+2`.
If b=0, F=`0112` has prefix mass (1,2,0)
at p=3, while G=`12012` has (1,1,1).
Thus D>2 for (1,0). If b>=1 the positive
level-two witness above meets the only candidate index.

**Level three, a>=2,b=0.** Here
`B=1^a 2`, `F=AB`, `G=B^a C`, `H=ABC`,
and the true third words are `FG`, `G^a H`, `FGH`.
It suffices to compare the first two.
Put `K=a(a+1)`, `P=K+a+3`, and
`L=|FG|=K+a+6`.
In FG the zeros occur at positions 0 and P.
In G^a H the first zero occurs at K and the
second at `2K+3>L−1` for every a>=2.
Apart from the empty cut p=0, matching zero counts on
the entire legitimate range 0<=p<L is therefore possible
**only** for `K+1<=p<=P`.

On this interval, exact counting of the occurrences of
letter 2 in the actual B blocks and the trailing C gives:

| Prefix index p | #2 in FG prefix | #2 in G^a H prefix |
| --- | ---: | ---: |
| p=K+1 | a−1 | a |
| p=K+2 | a | a |
| K+3<=p<=P−1 | a | a+1 |
| p=P | a+1 | a+1 |

The only nonempty equal-Parikh indices are consequently
`p=K+2` and `p=P` (the 1-count follows from equal
length). At `K+2`, next letters are **1 versus 2**.
At `P`, next letters are **0 versus 2**. The
empty prefix p=0 has next letters **0 versus 1**.
Thus *no* common-prefix/next-letter witness between even
the first two sources exists at generation three, proving
D>=4 for every a>=2,b=0. Combined with #479's
true fourth-level witness, D=4.

The preceding exclusions are symbolic in a and b.
The bounded oracle's exhaustive lower-level searches
are independent regression checks, **not** the proof
of minimality for unbounded parameters.


## Prefix-satellite lifting and exact all-pairs depths

The family has an elementary but useful **word-level structure** which
does not follow from its incidence spectrum:

**Lemma (prefix-satellite lifting).** Let \(\tau\) be any nonerasing
substitution on an alphabet and suppose \(\tau(k)=\tau(i)W\) as
*literal words* for distinct source letters \(i,j,k\) and some word
\(W\) (possibly empty). For every \(n\geq1\),

\[
\tau^n(k)=\tau^n(i)\,\tau^{n-1}(W).
\]

Therefore every equal-Parikh-prefix/common-next-letter witness for
the pair \((i,j)\) at depth \(n\) is *automatically* a simultaneous
witness for the triple \((i,j,k)\) at the **same cut and depth**.
Conversely every triple witness is a pair witness. In particular the
*minimum* simultaneous triple depth equals the minimum pair depth
\(D_{ij}\), including the possibility that both are infinite.

**Proof.** Apply \(\tau^{n-1}\) to the literal word equation
\(\tau(k)=\tau(i)W\) and use multiplicativity of substitutions
under concatenation. The word \(\tau^n(i)\) is an exact prefix of
\(\tau^n(k)\); its Parikh prefix and next letter at every legal
cut agree with those for \(\tau^n(k)\). The equivalence is immediate.
No Pisot assumption, periodicity assumption, or finite BPA state
set is needed. The statement is *about a supplied prefix relation*,
not an assertion that such a relation always exists.

Here \(\sigma(2)=\sigma(0)2\) exactly; hence

\[
\sigma^n(2)=\sigma^n(0)\sigma^{n-1}(2).
\]

Thus the minimum simultaneous depth found above equals the minimum
ordinary **(0,1) strong-coincidence depth**, not just an upper bound.

**Corollary (sharp all-pairs coincidence depth).** For every member of
this forward family, the minimum strong-coincidence depth for the pair
\(\{0,2\}\) is **1**. For each of \(\{0,1\}\) and \(\{1,2\}\)
it equals the value \(D(a,b)\) in the five-chamber table above.
Consequently the minimum generation by which **all three pairs**
have individually become strongly coincident is *exactly* \(D(a,b)\).
This is stronger than an upper-bound certificate: the earliest
all-pairs level is explicit and it varies at fixed incidence.

**Proof.** At generation one, \(\sigma(0)=01\) and
\(\sigma(2)=012\) share the first letter 0 (the empty prefix).
The prefix-satellite lemma and the five-chamber lower bound give
\(D_{01}=D\) and a level-\(D\) certificate for \(\{1,2\}\).
It remains to exclude earlier \(\{1,2\}\) witnesses in the
chambers where \(D>2\).

At level one, \(\sigma(1)=B\) has **no zero** while
\(\sigma(2)=012\) starts with zero, so no witness exists:
at p=0 the first letters differ, and for p>0 the zero counts
cannot match.

At level two and \(a\geq2\), the true words are
\(G=B^aCB^b\) and \(H=ABC\). The former has just **one zero**
and the latter two. The first zero of G is at index
\(a(s+1)\), strictly *after* the second zero of H
at index \(s+3\), because \(a\geq2\), \(s\geq2\).
Before G reaches its first zero its prefixes have zero
zeros, while H already has at least one. Afterward,
G has one zero and H already has two. Hence there is
**not even a nonempty equal-Parikh-prefix cut**.
For \((a,b)=(1,0)\), the literal words are G=`12012`,
H=`0112012`; their only equal-Parikh-prefix indices
inside G are 0 and 4, and their next letters are respectively
1/0 and 2/0. This excludes level two on the last remaining
\(D>2\) boundary.

At level three for \(a\geq2,b=0\), use
\(Y=G^aH=\sigma^3(1)\), \(Z=FGH=\sigma^3(2)\), with
\(K=a(a+1)\), \(P=K+a+3\), \(L=K+a+6\). Up to cut
\(p\leq P\), Z has exactly the same prefix as
\(X=FG=\sigma^3(0)\), and the earlier proof classified
**all** balanced prefix cuts as 0,K+2,P, with mismatching
next letters. For p>P, separate the remaining parameter
regimes:

* \(a\geq4\): Z has at least two zeros, while Y has exactly
  one zero throughout its remaining comparison range
  \(p<|Z|=K+2a+12\). The *second* zero of Y appears at
  \(2K+3\geq|Z|\).
* \(a=3\): Z has a second zero at P=18, third at L=21
  and fourth at 27. Y has its second zero at 27.
  Thus from p=19 through 27, Z has more zeros than Y,
  and for p=28,29, Z has four while Y has two.
* \(a=2\): Z has zero positions 0,11,14,19;
  Y has zeros at 6,15,18 (the fourth occurs after Z ends).
  All p>11 have unequal zero counts **except p=19**.
  At p=19 the prefix difference
  \(\operatorname{Parikh}(Y[:19])-\operatorname{Parikh}(Z[:19])
    =(0,-1,1)\ne0\), ruling out that last candidate.

Therefore there is no \(\{1,2\}\) witness at any
generation below \(D\). At generation D the literal
three-letter certificate supplies one, completing the proof.

**Scope.** This pairwise-completeness argument depends on the exact
forward word order. The arbitrary prefix-satellite lemma is general,
but the five-chamber classification is not. Neither resolves C4
for unrelated primitive irreducible Pisot substitutions. It does
not claim that arbitrary balanced roots are *first* productive
at D; it only establishes a sharp worst-case letter-pair
strong-coincidence horizon.

### Ternary prefix-satellite exclusion criterion (general, sufficient)

For **any** nonerasing substitution on three letters i,j,k with literal
\(\tau(k)=\tau(i)W\), if the pair \(\{i,j\}\) has a
strong-coincidence witness at generation \(n\geq1\), then **every**
pair of distinct letters has a strong-coincidence witness by
generation \(n\). The proof does not need Pisot spectrum:
\(\{i,k\}\) share the initial letter of \(\tau(i)\) at
generation 1, while both \(\{i,j\}\) and \(\{j,k\}\) have
a witness at generation n by literal prefix lifting.

Moreover every **irreducible noncoincident Parikh-balanced word pair**
has distinct first source letters. Inflating it through the
appropriate pairwise witness puts adjacent balanced cuts around an
equal single letter in the complete factorization. Thus every such
balanced root has a diagonal descendant by generation n, and there
is **no nonempty fully strictly child-closed noncoincident
balanced-pair system** for this substitution, finite or otherwise.
The final assertion is a direct contradiction to complete strict
child closure, not an assertion of global BPA termination.

This is a *conditional* structural productivity criterion. It
does **not** prove that an arbitrary Pisot substitution has a
literal prefix-satellite pair, nor that the remaining pair ever
coincides. For the present family both hypotheses have been
proved uniformly; for general C4 they are new explicit premises,
not conclusions.

## Consequence and fixed-incidence correction

For each chamber, any nonempty irreducible noncoincident
balanced pair has a genuine one-letter diagonal in
its **complete** factorization by the specified generation,
exactly as in #479. This is a uniform *upper bound*
for every root, and is **not** an assertion that every
root requires D(a,b) generations.

For s=4 the sharp simultaneous witnesses become:

| a,b | Minimum generation | Exhibited p |
| --- | ---: | ---: |
| 0,4 | 2 | 0 |
| 1,3 | **2** (previous exhibit: 3) | 6 |
| 2,2 | 3 | 11 |
| 3,1 | 3 | 16 |
| 4,0 | 4 | 97 |

Hence even the **minimal simultaneous depth**
varies within the same full incidence matrix M_s
(and the same Perron/Pisot data), so an incidence-only
argument cannot determine it. Word order is essential.

## Execution, negative controls, trust boundary

* Canonical Mojo: the existing
  `kernel/psc/c4_third_level_coincidence_family.mojo`
  now has `verify_sharp_closed_run_coincidence`.
  It checks each displayed Q,z against *all three actual*
  full letter words, and exhaustively checks **every**
  smaller physical position at **every** earlier generation.
  The existing old positive-run and reversed family
  functions are intentionally unchanged. Its 0..16 input
  cap is for computation, not a hypothesis in the proof.
* Native regression:
  `kernel/tests/test_c4_third_level_coincidence_family.mojo`
  checks the five chambers, original compatibility,
  actual full balanced swap factors and input refusal.
* Independent Python:
  `tests/test_c4_forward_sharp_depth_oracle.py`
  reconstructs words without calling Mojo, checks all
  simultaneous cuts at all smaller generations for a
  9x9 nonzero parameter grid, the two new literal
  witnesses, the **complete** third-level balanced
  positions in the right-zero chamber, genuine swap
  factors, fixed-incidence depths, sharp **pairwise** earliest levels,
  literal prefix-satellite lifting, an equal-incidence/broken-order
  countercontrol, and invalid budgets.
* Negative controls: singular (0,0), negative/capped runs,
  earlier equal-Parikh positions with **different next
  letters**, and source pairs with earlier coincidences.
  No lower-depth inference comes solely from an
  incidence matrix or a first-letter endpoint mask.

Replay from the exact checkout:

```sh
python -m pytest -q tests/test_c4_forward_sharp_depth_oracle.py
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_third_level_coincidence_family.mojo)
python tools/make_proof_bank.py --check
```

No general strict C4 carrier or new G1/BH/A1′ conclusion follows.
No change to the governed PSC theorem status is requested.
Local finite tests, hosted exact-head CI and external
mathematical review are separate acceptance layers.
