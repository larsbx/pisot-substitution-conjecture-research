# Exact selected-rank soundness, separate from graph completeness

**Status:** native Mojo checker plus independently written Python reference;
a mathematically elementary well-founded descent lemma is given here.
No new Lean kernel theorem, actual hosted Mojo pass, all-parameter
class-A descendant productivity, global strict-zipper boundary hitting,
G1 or Pisot Substitution Conjecture is claimed.

## Why this interface is necessary

PRs #434/#435 produced shortest-path rank forests on completed finite
reversal-orbit quotients. Their *logical* kernel is substantially
smaller than those finite graph searches:

* A list of genuine overlap states and their actual selected indexed
  child transitions does **not** need a *complete outgoing star*
  to establish coincidence productivity for the **listed** states.
* A closed/capped/partial graph must **not** be used to infer
  productivity of *every reachable* vertex unless completeness and
  forward-coverage are independently proved.
* A shortest-path/BFS producer is untrusted. Checking a selected
  rank-decreasing witness is enough to justify the exhibited path,
  without using BFS or a claimed full SCC classification.

The canonical new module is
`kernel/psc/selected_rank.mojo`. Python under
`reference/psc_research/selected_rank.py` is a secondary,
independently written oracle with negative controls.

## Precise soundness statement

Let V be a set of enumerated states, E a relation of
**genuine actual directed child occurrences**, T the states which
are genuine equal-letter full-zero typed coincidences, and
r:V->nonnegative integers a proposed rank. Suppose

1. r(v)=0 if and only if v belongs to T;
2. for each v with r(v)>0, a recorded actual indexed edge
   v->w satisfies r(w)=r(v)-1.

Then for **each listed** v there is an actual selected path
of exactly r(v) edges ending in a typed coincidence.
Proof: induction on the nonnegative integer r(v),
following the recorded edge until rank zero.
No SCC, spectral, continuity, finiteness-of-all-overlaps,
or arbitrary-child termination premise is needed.
The theorem applies to a finite certified carrier
and to any symbolically specified well-founded family
when those indexed-edge premises are proved uniformly.

**What it does not say:** an arbitrary set of two vertices
with a valid rank certificate need not include a third
overlap vertex that can be reached from a seed.
The code thus distinguishes a selected-path certificate
from **completeness of the seed's forward closure**.
No capped finite state graph can be called universally
productive by pretending its seen vertices are all vertices.

## Native exact-word binding

`verify_rank_forest` checks shape, all adjacency destinations,
the independently supplied typed-terminal mask, nonnegative ranks,
real selected adjacency positions and exact one-step descent.
It fails closed instead of truncating a path or accepting an
undefined target. It uses the safe identity
`rank(child)=rank(source)-1` rather than incrementing a possibly
overflowing machine integer.

`verify_overlap_rank_witness` then derives terminal markers
**from the original exact cubic-field OverlapState**:
`top==bottom && shift.is_zero()`. It recomputes the selected
`(top occurrence,bottom occurrence)` against
`SeedOverlapTables` and `selected_overlap_child`, which
use the actual literal images and exact proper prefixes, and
independently requires **strict physical overlap** of source
and child. It rejects a wrong Parikh/shift target even when
a numeric state-ID edge happens to exist.

`verify_complete_overlap_rank` also rejects
`SeedOverlapAutomaton.capped`. However, *an arbitrary caller*
can fabricate an incomplete automaton marked `capped=False`;
that boolean is **not itself a completeness proof**.
A universal all-descendants result additionally requires
the authoritative exact closure builder or a proof that the
symbolic carrier is complete under every indexed child.

Note: the older Python class-A `(top,bottom,dx,dc,dy)` oracle
and native cubic-field `OverlapState(top,bottom,shift)` use
different representations. Their geometric equivalence is
not silently assumed by this generic verifier.

## Regression plan and trust boundaries

The native test `kernel/tests/test_selected_rank.mojo` checks
a valid finite forest, a genuine actual selected child leading
to typed coincidence in a three-letter determinant-two
calibration, and adversarial mutations: negative/false rank,
wrong source/target and terminal, wrong ordered child indices,
a directed nonproductive self-cycle, malformed adjacency and
a capped graph. The Python reference verifies analogous cases,
including that a successful certificate on two listed vertices
provides **no assertion about an unlisted third vertex**.

The dedicated workflow uses the repository's lockfile-matched
Mojo runtime and separately executes the Python reference.
The native compiler is not available in the present local
environment; do not claim a Mojo compile pass or proof-bank
acceptance until exact-head hosted execution and review succeed.

## Next true mathematical obligation

To use selected ranks for the still-open minus class-A X closure,
one must synthesize a **complete parameterized quotient carrier**
and prove, for every k,t>=0, that each actual child either
belongs to that carrier (or has an explicitly handled exit).
Only then can a well-founded rank forest give a *universal*
all-X-descendant productivity theorem.

The source-local rank-soundness lemma in this packet is
not itself a global graph-coverage result. PRs #428–#435
retain their original scope. No proof bank status, signed
receipt, archived research packet, canonical claim ledger or
unaccepted general theorem is modified.
