# Proof-carrying finite coincidence ranks on the exact class-A reversal quotient

**Status:** new, separately verifiable **finite-graph** proof certificates and
an elementary universally valid graph-rank lemma. Stacked on PR #434's
reversal-orbit quotient, which in turn depends on #433; universal reversal
invariance of the forward X closure is separately proposed in #432.
The certificates prove productivity **only for the explicitly completed
finite specimen graphs**. No parameter-uniform rank, G1, BH/#139 or
general Pisot Substitution Conjecture conclusion is claimed.

## Exact witness format and the graph lemma

The input is an *actual, completed*, strict indexed-overlap graph.
PR #434 forms its reversal quotient with one canonical representative
per orbit [w]={w,R(w)}; every quotient edge stores a genuine
(top occurrence index,bottom occurrence index, child orbit).
Typed full-zero coincidences are terminal, and the reversed
actual transition is always available by swapping indices.

A certificate is a list with **one row per quotient orbit**, containing:

    { "label": [top,bottom,dx,dc,dy],
      "rank": nonnegative integer,
      "edge": null  OR  [top_index,bottom_index,typed_child_orbit] }

The independent checker demands (a) complete, unique coverage of
all quotient states; (b) **rank zero if and only if the orbit is a
genuine typed coincidence**, with no outgoing chosen edge;
(c) each other orbit has positive integer rank; and
(d) its displayed actual indexed edge is in the complete
quotient adjacency and targets a state of rank **exactly one less**.
These finite tests imply that repeatedly choosing the certified
edge must hit typed coincidence after precisely the displayed
number of steps. Because PR #434 proves the quotient-edge
lifting lemma, the same certificate yields a genuine strict
indexed overlap path from **either actual orientation** of
every state to typed coincidence.

The implication is a standard finite integer induction
and is valid for any complete reversal-equivariant
overlap graph. The new contribution is an executable
**proof-carrying witness format and verifier**, not an
assertion of a newly discovered abstract graph theorem.
The verifier does **not** compute BFS or assume a
productive SCC: the producer uses reverse-BFS merely to
propose ranks, while the independent verifier checks
the actual indexed edges and rank inequalities directly.

A nonproductive directed cycle is refused: its vertices
cannot receive a complete decreasing-rank witness.
A capped overlap graph is never accepted as a completed
graph by the original graph builder.

## Exact locally executed finite certificates

The new source `oracles/python/class_a_reversal_rank_certificate.py`
calls PR #434's strict reversal-quotient builder and generates
deterministic canonical rows. After independent rank verification,
it lifts the selected path from **every original vertex**
using the unchanged literal substitution words, full
bottom-minus-top Parikh coordinates and exact Fraction/Perron
strict-overlap guards. All tests distinguish true
RUN from LAST occurrences and retain original ordered indices.

For each k,t in {0,1,2,3}, both the **complete forward-X**
graph and the **complete 18-orientation swapped-patch**
graph received a fully checked finite rank certificate.
The resulting quotient sizes and maximal selected ranks are:

| k,t | X quotient orbits | 18-seed quotient orbits | maximal rank |
| --- | ---: | ---: | ---: |
| 0,0 | 393 | 393 | 7 |
| 0,1 | 506 | 506 | 8 |
| 0,2 | 611 | 611 | 8 |
| 0,3 | 720 | 721 | 8 |
| 1,0 | 219 | 219 | 4 |
| 1,1 | 322 | 322 | 6 |
| 1,2 | 323 | 324 | 5 |
| 1,3 | 419 | 419 | 5 |
| 2,0 | 190 | 190 | 5 |
| 2,1 | 195 | 196 | 4 |
| 2,2 | 298 | 298 | 5 |
| 2,3 | 284 | 285 | 4 |
| 3,0 | 176 | 177 | 4 |
| 3,1 | 171 | 172 | 4 |
| 3,2 | 181 | 182 | 4 |
| 3,3 | 274 | 275 | 4 |

Every quotient has two terminal orbits (x/x, y/y),
so each completed X graph has exactly
`number_of_quotient_orbits - 2` selected decreasing
indexed occurrence edges in its proof-carrying forest.
This is a **chosen** subgraph, not an all-edge decreasing
rank: the original graph contains productive cycles.

For the (k,t)=(3,0) member:

* X closure: **350 actual vertices / 176 quotient orbits**;
  174 chosen indexed edges, maximum rank 4.
  Lifting every actual source produces **822 genuine
  word/Parikh/strict edges** along the selected paths.
* Orientation-complete 18-seed closure: **352 actual vertices /
  177 quotient orbits**, 175 chosen edges, maximum rank 4.
  Lifting every actual source produces **826 genuine edges**.

Deterministic canonical SHA-256 manifest hashes for the complete
sorted proof-row arrays at that exact parameter are

    X:   8cd230e84bad9b4193fda3e9a00943b29dd4698e192685db7357d55173c14722
    S18: 6e1dd938571c1bfe71e841fb694a30653eb565b5f327ac4588ff653dfa12973b

These hashes identify exact specimen-level *witness proposals*
and are not independent proofs or substitutes for the verifier.
The `--full` CLI outputs all canonical rank and actual
occurrence rows as inspectable JSON; default CLI emits
the counters, verified actual lifts, and digest.

## Negative controls and reproducibility

Five tests were executed locally as three separate successful
groups. The 16 X graph certificates and 16 S18 graph certificates
passed independently; a third group checked exact manifest
bytes, all-source word lifts, corrupt ranks, corrupt indexed
edges, missing rows, a symmetric nonproductive cycle,
truncated graph caps and invalid parameters.

The source and test file Git blobs are **byte-identical**
to the locally executed implementations:

    oracles/python/class_a_reversal_rank_certificate.py
      beff07e0175037b051e4d47f6a25a118a4624634
    tests/test_class_a_reversal_rank_certificate.py
      4e85573a3cfe4c9327179d66c60bdadc2cba306e

The dedicated CI workflow runs the groups separately
and must repeat them against the actual parent PR
implementation and repository's unchanged Geometry.
Fresh exact-head hosted gates and independent human
review remain pending.

## Next proof obligation: replace a finite array with a symbolic rank

For an actual **all-parameter** result one would need:
(1) a parameterized and **complete** description of
the quotient states in the forward X closure;
(2) a finite collection of exact integer parameter
chambers/rays describing their full actual child
occurrences; and (3) a symbolic nonnegative rank
with a genuine chosen edge decreasing by one
(or a verified stratified well-founded ordering).

The finite rank forests give inspectable candidate
data for **discovering** such a symbolic family, but
cannot by themselves establish a uniform parameter
rank or universal finiteness. This is the still-open
X-descendant productivity problem. Transfer to all
realized overlap classes, A1-prime, G1, BH and PSC
remains a further separate obligation.
