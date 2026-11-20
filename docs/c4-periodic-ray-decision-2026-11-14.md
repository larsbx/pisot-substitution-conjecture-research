# Deciding finite strict systems from periodic first-letter rays

**Status:** repository-proved per-source criterion; human review pending.

This continuation of [issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461) gives a per-substitution test uniform over the size of a supplied strict component. Its input is the literal substitution. See the [pre-code source review](c4-periodic-ray-decision-stop-go-2026-11-14.md) for the relation to Sirvent–Solomyak's half-coincidence criterion and the repository's bounded-gap reduction.

## Hypotheses and the finite test

Let `σ` be a primitive irreducible Pisot substitution, with column incidence `M`,
Perron root `β>1`, and positive left Perron lengths `ℓ`. The proof applies in
any finite alphabet dimension with irreducible Pisot characteristic polynomial.
The executable is ternary. The lengths are rationally independent by
irreducibility: a rational vector orthogonal to `ℓ` would have its entire
`M`-orbit in the kernel of `ℓ`, while a nonzero rational vector is cyclic.
Consequently common vertices in two patches with a common origin are exactly
equal-Parikh prefix cuts.

Write `g(a)=first(σ(a))`. For each unordered pair of distinct cyclic letters
`a,b` of `g`, take the actual overlap root `r=(a,b,0)`. Fix track order.
The shift of an overlap is the bottom start minus the top start. Each
ordered pair of child occurrences with prefixes `P,Q` supplies an edge
exactly when their tiles overlap with positive interior, with shift
`βt+ℓ(Parikh(Q)-Parikh(P))`. Retain repeated occurrences.

There are two targets:

- A **diagonal** has equal letter labels and zero shift.
- A **common endpoint** has zero shift or shift `ℓ(top)-ℓ(bottom)`, so the
  two starts or the two ends agree. The overlap interval is closed when
  evaluating endpoints, even though its length must be positive to enter the
  graph. An end-to-start contact has no positive interior and supplies no edge.

**Theorem (periodic-ray criterion).** A finite strict system exists if and
only if at least one such root
satisfies both conditions:

1. No reachable overlap is diagonal.
2. Every reachable overlap has a path to a common endpoint.

These are finite tests for each fixed `σ`. They do not require a bound on
the unknown word lengths, a graph of all hull overlaps, or a unit assumption.

## Why the graph is finite and complete

Store shifts as `t=ℓw` for `w∈ℤ^d`; each child uses the exact recurrence
`w'=Mw+Parikh(Q)-Parikh(P)` and the initial register is zero. In each
contracting conjugate the shift remains bounded by the corresponding
finite digit bound divided by one minus the modulus of the conjugate.
The physical shift stays between `-ℓ(bottom)` and `ℓ(top)`. The image of
the integral module under the full embeddings is a lattice, since the
lengths form a rational basis of the Perron field. The bounded region
therefore contains only finitely many shifts.

Inductively the descendants of `r` at depth `n` are precisely the
positive-interior overlaps of `σ^n(a)` and `σ^n(b)` with common origin.
Every child is contained in its parent on both tracks after inflation,
and every actual descendant occurrence specifies those parents.
Translation by the two real starts gives exactly the recurrence above.
Hence an overlap type's path can be replayed inside any of its
occurrences, including repeated types. A diagonal persists by
nonerasure. The implementation may therefore treat diagonals as terminal
when deciding reachability. If the root never reaches one, the entire
reachable graph has complete outgoing rows.

## From a strict system to a periodic pair

Select the first literal balanced child of every ordered state. Nonerasing
images ensure the selector is defined. On the finite set it has a cycle.
If its length is `m`, a state `(u,v)` on that cycle is a two-track prefix
of `(σ^m(u),σ^m(v))`. If the given component uses representatives up to
swapping, take its ordered swap closure first. This accounts for either
orientation of a cycle.

The first letters `a,b` of `u,v` differ because the state is irreducible
and noncoincident. Both are fixed by `g^m`. The infinite rays `X_a,X_b`
are the nested limits of `σ^{km}(a),σ^{km}(b)`. Those prefixes grow
without bound and lie inside the nested prefixes `σ^{km}(u),σ^{km}(v)`.
Thus the latter words exhaust the same rays. At every such finite level
the complete factors lie in the strict system, so the two rays have no
common tile and their common vertices have bounded gaps.

Any graph diagonal at depth `n` would survive to a level divisible by
`m` and occur on the two rays, a contradiction. If a reached overlap
has no path to a common endpoint, let its occurrence have positive
length `δ` and occur at depth `n`. For arbitrarily large `j` with
`n+j` divisible by `m`, the scaled overlap interval has length
`β^jδ` on the two rays and contains no common vertex. Indeed an interior
common vertex is the common start of two right-hand descendants.
A common vertex at the left or right endpoint would be respectively a
common start of the first descendants or a common end of the last
descendants. Their intervals overlap positively. Either event would
supply the missing path. This contradicts bounded gaps.

## From a periodic pair to a strict system and a size bound

Suppose the two tests succeed. Choose a common positive cycle period
`m` of `a,b`. Every actual ray occurrence lies in sufficiently long
prefixes at depths divisible by `m`, so a common tile would be a
reachable diagonal. Put `D=max_v dist(v,common endpoint)` on the complete
rooted graph and choose the least multiple `n` of `m` with `n≥D`.
At each physical position use a positive overlap of the two rays whose
closure contains that position divided by `β^n`. Its type is reachable
and its length is at most `ℓ_max`. Follow an actual path of length at most
`D` to a common endpoint inside the scaled interval. Substitution preserves
that vertex through the remaining levels, and both rays are fixed by
`σ^n`. The original position is therefore within `β^n ℓ_max` of some
common vertex. Consecutive common vertices are at most `2β^n ℓ_max`
apart. This gives a factor length bound `B=floor(2β^nℓ_max/ℓ_min)`.

Let `C₀` be all the consecutive-cut blocks of the aligned rays.
They are nonempty, irreducible, balanced and noncoincident, and finite by
the length bound. Inflating a block by `σ^m` takes its endpoints to common
vertices of the same rays, so **every** complete `σ^m` factor is in `C₀`.
For one-step closure take the union of the complete block sets reached
from `C₀` at depths `0,…,m-1`. The existing composition of complete
factorizations shows that at the last phase all children land in `C₀`.
There are no diagonals at the extra phases: if one appeared, nonerasure
would carry it into the next depth divisible by `m`. This proves the
converse.

In a supplied strict SCC the cyclic first-factor root reaches every state
up to exchanging the tracks. Every state appears as a factor at some
depth; for a state that appears only at a specified phase, use the
corresponding pair of phase-shifted rays. The same bound applies in each
phase: each phase is fixed by `σ^m`, all its overlap types lie in the
rooted graph, and the same `D` works. Thus every state has length at most
`B`, independently of the component size. For an alphabet of size `d`
there are at most `Σ(j=1..B) d^(2j)` ordered word pairs of this length.

## Literal witnesses and replay

If a root is productive, its shortest overlap path gives two literal
source-letter digit lists ending in equal Parikh prefixes and an equal
letter. For a supplied irreducible balanced parent with these first
letters, pass those digits at source positions `(0,0)` to
[the addressed newborn theorem](c4-addressed-overlap-to-newborn-2026-11-04.md).
Its first diagonal supplies the required one-step interior newborn on a
parent reached by actual child ordinals. The local check for `01/12/021`
starts at `(01,10)`, uses ordinals `[0,0,1,0]`, and produces a
`Sync_-` at cut 1 of `(21120,02112)`.

[Canonical Mojo](../kernel/psc/c4_periodic_rays.mojo) reuses the existing
exact ordered overlap graph and reverse reachability. It uses a configurable
20,000-state ceiling by default. The inherited screened incidence bound,
arithmetic overflow, and a state cap all refuse an executable verdict.
The mathematical proof uses none of those numerical ceilings. The
[independent Python test](../tests/test_c4_periodic_rays_oracle.py)
reconstructs every fixture's graph from rational interval signs and checks
the literal witness by expanding both words with full occurrence addresses.
It checks the exact output rows of the native run. The fixtures include a
single cyclic letter, two distinct fixed letters, a two-cycle, a three-cycle,
a non-unit case, and a member of the parameter family. They supply six
productive pair rows. The reducible strict control `10/102/211` is refused
before any graph verdict. Separate controls distinguish a common right
endpoint from a left-aligned target and from a contact without interior.

```sh
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_periodic_rays.mojo) > /tmp/c4-periodic-rays.txt
PSC_PERIODIC_RAY_NATIVE=/tmp/c4-periodic-rays.txt python -m pytest tests/test_c4_periodic_rays_oracle.py
python tools/make_proof_bank.py --check
```

The remaining uniform question is whether every candidate ray pair for
every ternary PIP source either reaches a diagonal or has a reached overlap
with no common-endpoint descendant. For #461 it would suffice to establish
that disjunction under the ordered flat-hub hypotheses. An unbounded gap
rules out a finite strict system from that root, including cases where the
root itself has no coincidence. It supplies no general extraction from an
arbitrary failure, and no BH, A1′, G1, spectral or PSC claim is upgraded.
