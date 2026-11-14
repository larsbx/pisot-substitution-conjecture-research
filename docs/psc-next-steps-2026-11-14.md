# PSC next steps — November 14, 2026

**Priority: complete the two named termination acceptance gates, then extend
the proof mechanism to a precisely specified infinite family.** The positive
overlap argument, strict-system exclusion, forward carriers and termination
consumers already exist. Their source presence and their compiled acceptance
have different evidentiary scopes. This note changes no governed claim status
and authorizes no automatic merge or promotion.

## 1. Current source and acceptance boundary

| Item | Exact source or evidence | Established scope |
| --- | --- | --- |
| Open integration PR [#560](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/560) | `1ce54efeff586ecda2ec1bd11a2f9c6617b2fb87` | Contains the merged #561–#566 and #568 developments; targets `main`. Integration is not complete acceptance. |
| Historical failed head of [#569](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/569) | `52614a3b5a7199b1d17cb7a0b435da71e1e80569` | Formal verification failed at the named-carrier consumer after both generated carrier checkers compiled. |
| Historical named strict exclusion | `bb6cbac16a620da4784f5b30d0a9a242618aef22`; [run 43365333027](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43365333027) | Successful complete original-archive replay at seven semantic endpoints, including exclusion of every finite strict system for each literal fixture. |
| Current selector-transport repair in [#569](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/569) | `8a6bd5732fefba94ad4fef5df2333065c1302452`; tree `a7dcb3ebf30f3bb686d8f1beb3545dec26df8448` | Uses generic vector-selection lemmas and explicit literal-substitution transport, with the generated checkers' recursion allowance scoped to this one theorem. The preceding explicit-only candidate `84f7b2b7` failed at its selector equality; complete successor acceptance remains pending. |

The historical strict-exclusion result is preserved at its own revision.
Neither it nor successful native forward replay certifies a later modified
Lean consumer. Earlier failures remain failures. The
[November 13 acceptance note](c4-named-termination-acceptance-2026-11-13.md)
retains the preceding diagnostic history, including both hosted carrier
compilations followed by the consumer recursion error.

The explicit-only candidate `84f7b2b70adbd632c0e0cc06cbd246aee2020f70` also failed at the fixture-1 selector equality after both carriers compiled. The current repair addresses that same proof-transport boundary with a theorem-local recursion allowance. It must
preserve both literal substitutions, every carrier word and complete child
row, the checker predicate, theorem statement and axiom allowlist. This is a
regression repair to an already reviewed contract; the existing literature
decisions apply. It receives acceptance only after the actual production
module and its downstream consumers compile successfully.

At `52614a3`, the [full Lean run 43492499736](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43492499736)
and [archive run 43492499714](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43492499714)
compiled both generated carrier checkers, then reported maximum recursion
depth at `NamedForwardCarrier.lean:77:10`. The
[#560 archive run 43447323834](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43447323834)
had the same failure at `77:4`. These are elaboration failures, not timeouts;
the later nine-endpoint archive imports were not reached.

## 2. Complete the two-fixture proof chain

The intended result concerns exactly `1/021/001` and `1/012/001`. Their
canonical Mojo exports supply finite ordered carriers with 192 and 520
states, respectively. Native construction and independent replay preserve
all six unequal ordered swap seeds and all actual child occurrences. A
finite closed superset suffices; these carrier sizes are not claims of
minimality. See [the forward-carrier contract](c4-forward-carrier.md).

The proof has two independent inputs. Checked forward closure supplies
finite actual `ChildNC` reachability. The original validated inverse-overlap
archive supplies strict-system exclusion for the same literal substitution.
The [finite-productivity bridge](c4-finite-productivity.md) then proves
termination with coincidence for every actual descendant of every ordered
swap seed. An inverse archive cannot replace the forward carrier, and
incidence-matrix equality cannot replace literal word-order binding.

The required next checks, in order, are:

1. Compile the repaired production `NamedForwardCarrier` against both actual
   generated carriers, then inspect its exact theorem types and transitive
   axioms. Preserve a reproducer of the preceding recursion failure.
2. Run the unchanged isolated full-library build and compiled proof-bank
   audit on the published source revision.
3. Replay both original archives at all nine endpoints: `valid`, `accepted`,
   `typed_accepted`, `domain_iff`, `roots_null`, `ancestors_null`,
   `no_strict_system`, `seed_terminates` and `reachable_terminates`.
4. Inspect the final artifacts and negative controls, record successful
   terminal results with exact source identity, and check the final
   integration revision's relevant governance and repository gates.

Canonical commands and artifact requirements are in the
[acceptance note](c4-named-termination-acceptance-2026-11-13.md#replay).
Missing endpoints, wrong literal types, omitted exits, changed orientation,
disallowed axioms and nonterminal jobs must refuse acceptance. Resource
limits remain inconclusive. A complete successful result would establish
the stated two-fixture theorem; independent human review remains separate
validation debt, and merge decisions remain with the user.

Here, termination with coincidence means finite actual reachability and an
existing coincidence-reaching path from every reached state. It does not
assert that every possible path eventually reaches coincidence, or cover an
arbitrary starting block outside the checked seed-generated set.

## 3. Reuse the completed measure argument

The [positive-overlap bridge](c4-positive-overlap.md) is already implemented
in `NamedPositiveOverlap.lean`. It compares the same original integer-cut
finset in both bounds, retains one common positive cell mass, fixes the
packing depth before increasing the word generation, and transfers open
lower bounds through outer regularity. The finite strict carrier supplies
its own positive maximum source length.

The [strict-exclusion composition](c4-named-strict-exclusion.md) covers its
represented distinct-letter intersections by the three original zero-offset
roots. Their checked nullity contradicts that positive measure, using one
shared product measure. Probability Haar existence is discharged internally.
Reimplementing those steps would duplicate completed work. The next extension
must identify which remaining fixture-specific hypothesis it discharges.

## 4. Next mathematical target after acceptance

A subsequent [four-source family review](c4-parameter-family-stop-go-2026-11-14.md)
redirects the first concrete candidate `sigma_k=(1,0 1^k 2,001)`: existing
prefix-witness lemmas already give the hand-derived strict-exclusion route for
`k>=2`. Subject to the remaining prior-coverage/conjugacy identification
check, its useful target is finite actual `ChildNC` reachability from seed
`01/10`, allowing a parameter-dependent carrier bound. The exact
word identities, boundary cases, prior-coverage checks and uncompiled scope
are recorded in that review. No family Lean acceptance is claimed.

The broader geometric programme below remains available for families without
such an already applicable coincidence mechanism.

Select one explicitly defined infinite substitution family and seek a
**uniform, occurrence-preserving root-nullity or source-loss certificate**
for every admissible parameter. The first deliverable is a written family
definition, exact hypotheses and a targeted stop/go review of three to six
primary sources, following [AGENTS.md](../AGENTS.md). Read the append-only
[side-notes ledger](side-notes-ledger.md) before selecting the mechanism.

The proposed certificate must retain actual prefix tiles and their complete
equations, a faithful physical/stable/integral chart, nonunit matrix-adic
coordinates, complete representation of nonempty incoming ancestors, and
every positional occurrence in the overlap recurrence. It must justify the
loss that forces root nullity throughout the family. Removing an occurrence
or assuming a positive deficit cannot supply that argument.

A successful abstraction of the existing geometry is reusable infrastructure;
its unproved family premises remain obligations. Extra finite specimens,
shared incidence data or parameter samples cannot establish the infinite
quantifier. Any new executable support belongs in canonical Mojo, with
independent oracle checks where useful and explicit refusal on incomplete
searches. Record a failed proposed invariant at its actual scope.

## 5. Universal completion remains separate

The direct route still requires universal one-sided residual
[A1′ (#138)](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/138)
and existential, occurrence-compatible
[BH (#139)](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/139).
Their existing assembly yields
[one-seed productivity (#84)](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/84)
and then the stated PDS conclusion. The alternate
[C4 target (#461)](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461)
still needs a uniform theorem on a supplied complete strict PIP component;
global finite-BPA extraction is a separate obligation where required.

The two-fixture chain supplies none of these universal quantifiers. General
A1′, BH, C4, G1 and PSC therefore retain their existing open status.
