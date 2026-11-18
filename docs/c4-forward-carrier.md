# Checking finite forward balanced-pair carriers

This increment supplies a finite-carrier checker whose soundness concerns
the actual ordered `ChildNC` relation. Its specification takes a literal
list of word pairs and checks their actual children for the supplied
substitution. The concrete indexed refinement proves the same
specification from checked irreducible blocks and literal factor rows.
A search-completeness flag and swap normalization are not premises of
either soundness theorem.

The generic source is
[`ForwardCarrier.lean`](../proof/PscVerif/PscVerif/ForwardCarrier.lean),
and the fixture-bound consumers are in
[`NamedForwardCarrier.lean`](../proof/PscVerif/PscVerif/NamedForwardCarrier.lean).
The [pre-code decision](c4-forward-carrier-literature-2026-11-12.md)
records the fresh three-primary-source check and the permitted scope.
The [verification-refinement addendum](c4-forward-carrier-fast-addendum-2026-11-12.md)
records the subsequent performance design before its implementation.

## Work shown

### Assumptions and hypotheses

The generic checker takes a finite alphabet with decidable equality, a
substitution `s`, and `states : List (List alpha x List alpha)`. Its
decidable proposition `ForwardCarrier.Valid s states` requires:

1. every member of the existing ordered `Descendants.seeds` belongs to
   `states`;
2. for every listed pair `T` with unequal tracks, every actual member of
   `red (subst s T.1) (subst s T.2)` belongs to `states`.

`ForwardCarrier.check` is the finite decision procedure for precisely
this proposition. It uses no classical decision instance. Coincidences
are terminal, so their inflated reductions impose no closure obligation.
The criterion does not require nonerasure, primitivity, Pisot expansion,
an incidence calculation or a geometric model.

The checked list can include duplicate or unreachable states. It need
not prove that every listed pair is an irreducible balanced block: its
role is a finite upper bound. Actual descendants of the swap seeds are
blocks by the existing source theorem. The termination consumer for an
arbitrary listed starting pair separately requires `IsBlock`.

### Derivation / reduction

Interpret `states` as the finite set of its list members. A successful
check gives closure under `ChildNC` directly because that relation means
an unequal-track parent together with membership in its actual reduction.
Induction on `ReflTransGen (ChildNC s)` shows that every finite path from
a listed state remains in the list. Thus the actual reachable set of
every listed state is finite.

For seed-generated reachability, use the existing
`Descendants.bpaStatesNC_subset` with the two checked clauses. This gives
containment of `bpaStatesNC s` in the finite list and hence its finiteness.
The existing `finite_bpaStates_iff` also gives finiteness of the full
child graph, but does not identify its states with the terminal-child
list: extra diagonal descendants may occur.

`NamedForwardCarrier.check fixture states` fixes `s` to the literal
`NamedPrefixCompact.substitution fixture`. The conditional
`finite_bpaStatesNC_of_check` theorem requires a successful check for this
expression. The packet termination wrappers additionally require the
original archive's `Packet.Valid` proof, which supplies strict-system
exclusion through the earlier
[finite-productivity bridge](c4-finite-productivity.md). The two
independent inputs are therefore explicit: checked forward closure and
validated strict exclusion.

The canonical Mojo engine uses representatives up to track swap. Its
proposed payload must include the ordered double cover; the Lean checker
verifies all ordered seeds and all raw children itself. No theorem
equating the normalized graph to Lean's ordered graph is trusted.

#### Concrete named binding: source pending acceptance

The generated sources
[`NamedForwardCarrierData0.lean`](../proof/PscVerif/PscVerif/NamedForwardCarrierData0.lean)
and
[`NamedForwardCarrierData1.lean`](../proof/PscVerif/PscVerif/NamedForwardCarrierData1.lean)
state their checks for literal substitution functions. The named wrapper
identifies those functions definitionally with
`NamedPrefixCompact.substitution 0` and `substitution 1`: their images are
respectively `1/021/001` and `1/012/001`, including the different order in
the middle image. No incidence-only identification is used.

`checkedStates fixture` selects the corresponding generated literal list.
`check_checkedStates` transports its generated `ForwardCheck` theorem to
the canonical named expression. The unconditional
`NamedForwardCarrier.finite_bpaStatesNC fixture` statement then binds the
generated `Finite` theorem to that same expression. Finiteness needs no
archive premise. Its proof still depends on successful compilation and
acceptance of the concrete generated proof terms; merely writing the
wrapper does not discharge them.

`Packet.seed_terminates` and `Packet.reachable_terminates` specialize the
existing conditional consumers with this checked list. They retain
`hp : p.Valid` and respectively membership in the actual ordered seeds
or `bpaStatesNC (substitution p.fixture)`. They cover every actual finite
`ChildNC` descendant of those seeds. They assert nothing about a starting
block outside that seed-generated set.

### Evidence and replay

The generic module contains nine structural/checker theorems and six
literal controls. The generic checker, fast refinement and separate
packet-control module have focused development compilations and a
separate successful scoped transitive-axiom audit. The fast addendum
records their scope and source hashes. The audit covers 172 owned
declarations and reaches all 50 source proofs in those three modules;
it excludes the concrete data and named wrapper. These are not a
complete isolated aggregate acceptance receipt.

The concrete generated data and the extended named-wrapper source remain
pending their own compiled acceptance. The first fixture-1 attempt using
plain `by decide` was stopped after about 299 seconds without completing;
it supplies no accepted theorem. Regeneration with the pinned ordinary
`decide +kernel` mode preserves the semantic packet and still requires a
recorded successful outcome. No heavy named-chain compile was launched
for the wrapper extension while the existing acceptance runs were active.
The second fixture-1 attempt using `decide +kernel` was killed with
return code -9 after 296.223 seconds, without an output object or Lean
error text. No cause was established, and no acceptance is credited.

The expected development replay, after provisioning the repository's
pinned toolchain, is:

```sh
(cd proof/PscVerif && lake build PscVerif.ForwardCarrier PscVerif.FastForwardCarrier PscVerif.FastForwardCarrierControls PscVerif.NamedForwardCarrier)
```

Complete aggregate and transitive-axiom acceptance still uses
`./tools/check_lean.sh` after integration. Record actual outcomes at their
source revision; these commands are instructions, not passed receipts.
Concrete generated states require their own checker equality proof and
the existing exact-source acceptance protocol.

Independent native/oracle replay retains complete ordered child rows,
including repeated factors and positions. The generic states-only
predicate does not authenticate proposed rows. The concrete fast
refinement separately checks each ordered row's two concatenations and
every child block, then uses `Reduction.red_unique` to prove equality
with the complete actual reduction, preserving order and multiplicity.
Neither route asserts exact discovery history or a minimal carrier.
The existing
[`target_packets._prepare`](../kernel/psc/target_packets.mojo) is a source
for the native row-replay contract.

### Negative controls

| Control | Guarded obligation |
| --- | --- |
| Empty Fibonacci list is rejected | Seed coverage cannot be replaced by vacuous closure. |
| Both Fibonacci seeds without their diagonal child are rejected | Every actual outgoing child must be covered. |
| Normalized Fibonacci representatives are rejected | The literal ordered carrier needs both orientations. |
| Three-state Fibonacci carrier is accepted | Coincidence states are terminal; `(1,1)` need not be included. |
| Fibonacci carrier with an extra terminal state and duplicate is accepted | A finite closed superset suffices; exact enumeration is not claimed. |
| Two-state Thue–Morse carrier is accepted | This checker certifies finiteness only. Its existing strict-system control proves nonproductivity separately. |

The last control is the genuine `0 -> 01, 1 -> 10` substitution, whose
existing `FiniteProductivity.thueMorse_finite_nonproductive` theorem
prevents inferring productivity from finite closure alone. It is not a
counterexample in the standing irreducible Pisot scope.

Named source binding must not be confused with carrier uniqueness. A
single list can legitimately pass for two substitutions if it is closed
under both actual child relations. A fixture-label mutation is not
guaranteed to fail the states-only predicate. The conclusion must use
the same literal fixture as its check; any independent exported-row
comparison must use the declared source as well.

### Non-claims / remaining gaps

Concrete named state lists, check statements and source-bound consumers
are now present in source, with compiled concrete and full named-chain
acceptance still pending. They assert no minimal carrier, exact carrier
size or exact discovery order. A capped search does not establish
finiteness or infinitude.

The named seed-generated finiteness conclusion receives credit only
after the actual literal data and their successful checks are accepted.
The termination consumers retain the archive's `Packet.Valid` premise,
which supplies the separate strict-system exclusion. Finiteness from
arbitrary unlisted balanced blocks, universal G1, general C4, pure
discrete spectrum and PSC are not established. Claim statuses remain
unchanged, and independent human review remains separate validation debt.
