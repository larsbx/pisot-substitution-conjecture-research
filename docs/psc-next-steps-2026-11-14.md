# PSC next steps — November 14, 2026

**Priority: complete acceptance of the infinite-family termination theorem,
then discharge its explicit spectral and arithmetic boundary.** The named
two-fixture chain has passed every relevant integration gate. The parameter
family now has a direct Lean construction of finite forward closure and
coincidence paths for every `k>=2`; see the
[formal family result and evidence](c4-parameter-family-carrier-2026-11-14.md#formal-termination-theorem).
Research continues with the existing human-review label carried as validation
debt. This note changes no governed claim status or merge decision.

## 1. Current source and acceptance boundary

| Item | Exact source or evidence | Established scope |
| --- | --- | --- |
| Open integration PR [#560](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/560) | `251079fc55c1fa7f6a9d3392e612c7e63132eefc` | Contains the merged #561–#566, #568 and #569 developments; targets `main`. Its tree is identical to the accepted `8a6bd573` source; the original run receipts retain their producing commit identity. |
| Historical failed head of [#569](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/569) | `52614a3b5a7199b1d17cb7a0b435da71e1e80569` | Formal verification failed at the named-carrier consumer after both generated carrier checkers compiled. |
| Historical named strict exclusion | `bb6cbac16a620da4784f5b30d0a9a242618aef22`; [run 43365333027](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43365333027) | Successful complete original-archive replay at seven semantic endpoints, including exclusion of every finite strict system for each literal fixture. |
| Accepted selector-transport repair in [#569](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/569) | `8a6bd5732fefba94ad4fef5df2333065c1302452`; tree `a7dcb3ebf30f3bb686d8f1beb3545dec26df8448` | Both the [full isolated audit](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43570948335) and [original nine-endpoint replay](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43570948106) succeeded. The unchanged inspector verified both original fixtures and controls. |

GitHub records [#569](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/569)
as merged by `larsbx` into #560 at 08:10:05 UTC on November 14. The
[merge commit](https://github.com/larsbx/pisot-substitution-conjecture-research/commit/251079fc55c1fa7f6a9d3392e612c7e63132eefc)
has tree `a7dcb3ebf30f3bb686d8f1beb3545dec26df8448`, exactly matching
the accepted proof source. The documentation/evidence follow-up [#570](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/570)
targets the #560 integration branch. Both #560 and #570 remain drafts;
`main` remains at `c9358c2d46d7b306853609e2c5a090328aff92c3` at this check.
Fresh integration receipts now also exist at `251079fc`: the
[full isolated Lean audit](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43574509547),
[original nine-endpoint archive replay](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43574509582),
[native forward-carrier replay](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43574509424),
and all 20 jobs in the
[broad research workflow](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43574509965)
completed successfully. These are the merge revision's own receipts, not
reassigned historical receipts. #571 subsequently merged its family word
identities into #570 at `dcfbef0808e3c5fc058a1e0c4f78c7f410630fde`.

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

The completed source-specific acceptance contract is:

1. Compile the repaired production `NamedForwardCarrier` against both actual
   generated carriers, then inspect its exact theorem types and transitive
   axioms. Preserve a reproducer of the preceding recursion failure.
2. Run the unchanged isolated full-library build and compiled proof-bank
   audit on the published source revision.
3. Replay both original archives at all nine endpoints: `valid`, `accepted`,
   `typed_accepted`, `domain_iff`, `roots_null`, `ancestors_null`,
   `no_strict_system`, `seed_terminates` and `reachable_terminates`.
4. Inspect the final artifacts and negative controls and record successful
   terminal results with exact source identity.

The repaired source has passed all four checks. Both compiled audits confirm
11,322 constants, 7,273 theorems, all 3,597 named source proofs and all 41
explicitly tracked declarations. Each original archive module passes all nine
endpoints, with 1,802 audited declarations and 779 theorem declarations; see the
[exact-source verification packet](../evidence/c4-followup-2026-11-14/README.md).
The original ZIP, transport binding, raw terminal metadata and unchanged
inspector output are preserved there. The newer `251079fc` integration runs
listed above discharge the previously pending integration checks, including
all 20 broad-workflow jobs. The historical 19/20 snapshot remains a historical
observation; it is no longer the current blocker.

Canonical commands and artifact requirements are in the
[acceptance note](c4-named-termination-acceptance-2026-11-13.md#replay).
Missing endpoints, wrong literal types, omitted exits, changed orientation,
disallowed axioms and nonterminal jobs must refuse acceptance. Resource
limits remain inconclusive. The complete successful result establishes
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

## 4. Infinite-family closure and next mathematical target

A subsequent [six-source family review](c4-parameter-family-stop-go-2026-11-14.md)
redirects the first concrete candidate `sigma_k=(1,0 1^k 2,001)`: existing
prefix-witness lemmas already give the hand-derived strict-exclusion route for
`k>=2`. The bounded prior-coverage screen found no applicable all-parameter
import. Its finite actual `ChildNC` reachability target from seed `01/10`
is implemented in the new
[`C4ParameterFamilyCarrier`](../proof/PscVerif/PscVerif/C4ParameterFamilyCarrier.lean)
module, together with direct productivity and the existing termination
predicate. The original review's hand-derived scope remains historical;
the [family packet](../evidence/c4-family-termination-2026-11-14/README.md)
records the new compilation and acceptance scope.
The trace-bound literature already covers PDS for `k=1,2`; retain `k=2` as
a control and focus the substantive infinite extension on `k>=3`. Direct
one-step nonerasing beta intertwiners are excluded by endpoint cycles, while
powers and more general recodings remain unresolved.
The recent compatible-substitution theorem inspected in that review requires
unimodularity and does not apply to this determinant-two family. The scoped
forward-closure result makes no exhaustive noncoverage or nonconjugacy claim.

The original family source `32015cfb9d0914cedc9867f3290ea4bcdbbbb3b7` has now
passed both jobs in the [dedicated family gate](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43625009731)
and the [full isolated Lean audit](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43625009501).
The latter inspected 11,854 constants, 7,747 theorem constants and all 3,774
named proofs. Its former pending status is historical.

The next proof increment now supplies the previously missing arithmetic and
correspondence: `C4ParameterFamilyPisot` proves the literal primitive
irreducible Pisot hypotheses for `k>=1`, `TerminationFactors` proves the
general single-seed full-iterate equivalence, and `C4ParameterFamilyBridge`
assembles the complete literal criterion inputs for `k>=2`. All three modules
and their independent exact-type audit compiled successfully in development.
New source-isolated hosted acceptance remains distinct from predecessor results.

The [family spectral account](c4-family-spectral-closure-2026-11-14.md)
reconstructs aperiodicity and finite local complexity and applies the published
Barge–Štimac–Williams implication. The analytic/topological theorem remains
external to Lean. The all-parameter family conclusion is not an all-substitution
result. The fresh [universal closure review](psc-universal-closure-review-2026-11-14.md)
identifies the remaining occurrence-level obstacle and the fixed factor-length
bound used by the accepted packing argument.

The mathematical priority is now the actual universal BH hit: for each cyclic
seed-reachable strict-zipper overlap, construct a composable sequence of literal
child occurrences reaching zero offset. Retain all prefix addresses and
orientation in `M^m w = p-q`; locally admissible correction digits alone are
insufficient. Once that obligation is proved, use the existing overlap-depth
argument to obtain bounded balanced-factor lengths. Residual one-sided A1′
remains the other universal assembly premise.

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

For a direct universal attack, #84 ranks BH first, then residual A1′;
BH alone also supplies the stated G1 implication. Issue #84 tracks their
assembly rather than a third independent proof search. The narrower named
and parameter-family work above does not replace either universal premise.

The two-fixture chain supplies none of these universal quantifiers. General
A1′, BH, C4, G1 and PSC therefore retain their existing open status.

The new binary control `0->00001, 1->011` tests a tempting generic shortcut:
its common prefix gives productivity, while defect growth rules out finite
seed reachability. It is outside the Pisot class. It demonstrates why the
generic strict-exclusion consumer keeps a finiteness premise; it does not
prove independence of those properties inside PIP or provide a PSC
counterexample. The new source and acceptance are documented in the
[universal review](psc-universal-closure-review-2026-11-14.md).
