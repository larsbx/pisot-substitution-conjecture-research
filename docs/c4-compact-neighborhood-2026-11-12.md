# Compact neighborhoods capture actual balanced cuts

Baseline: `main@bdf033f647f73f911a47260e8bdad5f2e96f3c7a`, after the merge of
PR #557. The preceding [literature gate](c4-compact-neighborhood-literature-2026-11-12.md)
was committed before theorem code as `571c8df9`.

This increment formalizes the compact-neighborhood step in Section 4 of the
[written counting bridge](c4-nonunit-madic-counting-bridge-2026-11-04.md).
It consumes the authentic prefix-witness theorem of #557 and compactness of
the named actual tiles. It supplies eventual containment in open covers;
the count and measure arguments remain separate.

## Verification status

The unchanged isolated `./tools/check_lean.sh` passed with exit code zero
at code commit `6915e8d592b7ea5cb7c6950249811e354dc6c3e7`, tree
`c79e97bdae1224068895afa9dcf6cca6d7fe9fbb`, on 2026-11-12 at
19:37:14 UTC. HEAD, tree and recorded source bytes were unchanged throughout
the run. The [evidence archive](../evidence/c4-compact-neighborhood-2026-11-12/README.md)
contains the terminal receipt, complete compressed raw log, exact source
inventory, declaration inspection and replay instructions.

| Completed check | Result |
| --- | --- |
| Full pinned Lean build | 9,023 jobs completed successfully |
| Compiled audit | 6,628 declarations, including 4,850 theorem constants |
| Exact new source inventory | All 23 explicit theorems and eight definitions matched once with their expected owners and kinds |
| New-module compiled inventory | 39 constants, including 31 theorem constants with compiler-generated auxiliaries |
| Axiom dependencies | Only `propext`, `Classical.choice` and `Quot.sound` |
| Proof bank | 126 governed claims, 2,693 named Lean proofs reached, 411 source openings |

Acceptance comes from the third fresh invocation. The first attempt lost
its session without a terminal result; the second exited one after cache
extraction exhausted disk space. Their original records remain archived
and receive no acceptance credit. A retained-workspace import also remains
diagnostic only. The successful run took 3,065.692 seconds.

Later archive, report and publication commits do not change the tested
proof sources. Publication provenance maps original commits to exact-tree
GitHub mirrors and preserves original commit objects in a restorable bundle;
the local gate is credited to its actual original code revision. Hosted
checks require their own observation at the published head. Independent
human review remains pending. No governed claim status changes.

Archive integration also adds the required `SHA256SUMS` metadata to the two
preceding cut-prefix evidence packets. All 78 existing files and their
historical manifests remain byte-for-byte unchanged. The new packet and
publication packet use the same exact-file-set checksum convention.

## Mathematical result and quantifiers

Fix either literal substitution `1/021/001` or `1/012/001`. Write `K_a` for
its own authenticated period-two prefix tile in the original product

\[
 G=\operatorname{Stable}\times H_M,
 \qquad I=\bigcup_{a\ne b}(K_a\cap K_b).
\]

The two substitutions have equal incidence, but their actual words and
prefix tiles are not identified. Given an open set `U` containing `I`, a
fixed finite source carrier `C`, and a supplied actual strict-system
witness on `C`, the main theorem gives

\[
 \exists N\;\forall n\ge N\;\forall T\in C\;
 \forall\text{ actual balanced-cut marks in }\sigma^{12n}(T),\quad x^\star\in U.
\]

Here `x` is the original common prefix Parikh vector. The marks retain
their full before/letter/after data. They are proper positions with a
following letter; the cut at zero is included. Strict-system membership
supplies distinct following letters through the existing literal
`strict_cut_labels` theorem. It is not replaced by a finite candidate mask,
and the theorem does not construct a strict system.

The carrier-specific refinement replaces `I` by the potentially smaller
`I_C`, the union of intersections indexed by the actual `CutPair C a b`
relation. Strict-system membership authenticates every cut label in that
relation. Thus a cover need not include unrepresented distinct-letter
intersections. This uses the same fixed-label compact transfer, with finite
filter intersections restricted to represented pairs.

The threshold is independent of the chosen carrier member, following
letters and actual marked positions. It depends on the open neighborhood
and the fixed carrier. The words cannot grow with `n`.

The stronger cover form accepts any open family `(U_i)` covering `I`.
It chooses a **finite subcover `J` first**, and then one `N` such that every
such deep cut is in some `U_i`, `i in J`. Empty intersections are permitted;
nonemptiness and positive measure are never implicit premises.

## Derivation

### The actual product neighborhood basis

For an integer-module endomorphism `M` and a normed additive commutative
stable factor `E`, the generic module defines

\[
 R_{\varepsilon,q}(x,y)
 \iff \|x_1-y_1\|<\varepsilon
       \ \land\ \operatorname{eval}_q(x_2)=\operatorname{eval}_q(y_2).
\]

The matrix-adic carrier is the existing subtype of compatible quotient
sequences. Its topology is induced from the product of discrete quotient
coordinates. It is not given a discrete topology as a whole.

A neighborhood in that product restricts only finitely many coordinates.
Each discrete-coordinate neighborhood can be reduced to the zero
singleton. Choose `q` at least as large as every restricted index. The
proved reduction identity implies that zero at `q` is zero at every such
shallower coordinate. A stable norm ball supplies `epsilon > 0`.
Consequently every zero-neighborhood in `G` contains

\[
 V_{\varepsilon,q}
 =\{d:\|d_1\|<\varepsilon,\ \operatorname{eval}_q(d_2)=0\}.
\]

Conversely these sets are zero-neighborhoods, by norm-ball openness and
continuity of the exact residue evaluation. No injectivity or finite
quotient premise is needed for this generic basis. Those stronger
arithmetic premises belong to the existing proof of named tile
compactness, not to the generic neighborhood argument.

### Compact intersections and uniform translation

For compact `K,L` and open `U` containing `K intersection L`, Mathlib's
`IsCompact.nhdsSet_inter_eq` provides neighborhoods `W_K,W_L` whose
intersection is contained in `U`. Continuity of addition and compactness
make translation uniform over each set: some zero-neighborhood `V` has
`K+V subset W_K` and `L+V subset W_L`.

Refine `V` to one `V_(epsilon,q)`. If `x` has a sufficiently close witness
`y in K` and another `z in L`, then `x-y` and `x-z` are in `V`. Thus `x`
belongs to `W_K intersection W_L`, hence to `U`.

This argument needs **no separately bounded or precompact set of common
cut points** and no local-compactness assumption. Compactness is applied
to the tile witnesses, and the actual topological group structure controls
their translates. The imported topological principle is standard; the
new formal binding concerns the original carrier and literal cuts.

### All actual cuts at one threshold

For a fixed label pair, compact transfer chooses `epsilon,q` before
`NamedCutProximity.eventually_all_prefixes_close` supplies thresholds for
the two fixed source words. That earlier theorem controls every actual
mark, with an authenticated same-letter point in the appropriate tile.
Exact balance identifies the cut vector in both tracks. The equality of
its depth-`q` quotient with the reference point is literally the residue
coordinate equality in `R_(epsilon,q)`.

Finite filter intersections combine the six distinct-letter label pairs,
then the members of `C`. There is no exchange of an infinite family
quantifier with the eventual threshold. `cutPoints` stores the resulting
set of original common cut points, and the strict-system adapter derives
label separation from actual carrier membership.

Finally, `I` is compact as a finite union of intersections of compact
tiles. Mathlib's finite-subcover theorem selects `J` from any supplied open
cover. Its open union is then an admissible `U` for the uniform cut theorem.

## Formal interfaces

The increment contains 23 explicit named theorems and eight definitions:
eight generic neighborhood proofs, twelve named-cut consequences, and three
independent counterexample theorems. All enter the existing full compiled
audit through the root project import.

| Module | Purpose |
| --- | --- |
| `CompactNeighborhood` | Single-depth carrier/product neighborhood basis and compact intersection transfer |
| `NamedCutNeighborhood` | Original named tile intersections, actual cut points, fixed-label and finite-carrier uniformity, finite open covers |
| `CompactNeighborhoodControls` | Independent exact counterexamples to dropping compactness, openness or finite-family uniformity |

The carrier-specific downstream declarations are
`NamedCutNeighborhood.eventually_carrierOverlap_strict_cuts_mem` and
`NamedCutNeighborhood.finite_carrierOverlap_cover_captures_strict_cuts`.
They use only the intersections indexed by actual `CutPair C` labels.
The all-distinct-label versions remain available as
`eventually_strict_carrier_cuts_mem` and
`finite_open_cover_captures_strict_cuts`.
The fixed-source all-distinct-pair corollary requires distinct actual
following letters explicitly. The conditional empty-overlap result only says that an empty
`I` would eventually exclude these distinct-letter cuts; it does not prove
that `I` is empty for either fixture.

## Controls and scope boundaries

1. **Openness is substantive.** Even for the compact singleton tiles
   `K=L={0}`, nonzero points can approach both tiles arbitrarily closely
   and remain outside their exact intersection. A singleton target cannot
   replace an open neighborhood.
2. **Closedness does not replace compactness.** In the real plane the axis
   `y=0` and hyperbola `xy=1` are closed and disjoint. The witnesses
   `(R,0)` and `(R,1/R)` can be arbitrarily close. The simultaneous
   thickening need not become empty without compactness.
3. **Pointwise control is not uniform over an infinite family.** Let
   `x_n(i)=1` if `i=n` and zero otherwise. Every fixed `i` is eventually
   zero, while at each `n` one point remains one. This guards the finite
   source-carrier hypothesis and the order of quantifiers.
4. The existing genuine-carrier control in `CutPrefixControls` keeps
   equality at depth `q` distinct from equality at `q+1` or in the inverse
   limit. A neighborhood may require a larger fixed residue depth.

These are interface counterexamples, not counterexamples to the standing
Pisot conjecture. This increment contains deductive topology and formal
controls, with no new executable numerical algorithm, census or finite
approximation being substituted for the universal result. Existing Mojo
witness construction and its independent oracle are unchanged.

## Replay and remaining obligations

From the repository root:

```sh
python tools/make_proof_bank.py --check
./tools/setup_lean.sh
./tools/check_lean.sh
```

The unchanged verifier copies only sources and configuration into an
isolated workspace, checks fresh dependency pins, uses the fixed upstream
source-hash Mathlib cache, builds the entire project and audits every local
compiled declaration. Narrow development compilation is not its substitute.
The existing overlap Lean workflow includes the new modules through the
root import and records the actual candidate head.

The next analytic obligations are the fixed-origin regular-cylinder
lattice count, the lattice covolume matched to the existing product-Haar
normalization, an original strict-cut density lower bound, and the
outer-cover measure argument.
Arbitrary measurable or half-open cylinder covers need a proved open
neighborhood inclusion before this transfer can consume them.

Reference witness ordinals can repeat. The future count must count the
original common integer Parikh cut vectors, not distinct anchored reference
ordinals. `cutPoints` is their image under `ambientStar`; no injectivity or
cardinality equality for that image is proved here. A literal integer cut-set
cardinality bound from the complete balanced-pair factorization is the next
small combinatorial bridge, before the separate lattice asymptotics. No positive product-Haar measure, all-packet
identification, C4, A1', BH, G1, PDS or PSC conclusion is promoted.
