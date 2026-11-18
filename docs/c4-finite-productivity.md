# From strict-system exclusion to finite BPA productivity

This increment connects the named strict-system exclusion to termination
with coincidence while keeping actual reachability finiteness explicit.
For either authenticated fixture and every irreducible balanced block,
termination with coincidence is equivalent to finite `ChildNC`
reachability. The result does not construct that finite reachable set.

## Work shown

### Assumptions and hypotheses

The generic theorem in
[`FiniteProductivity.lean`](../proof/PscVerif/PscVerif/FiniteProductivity.lean)
works for a substitution `s` on any alphabet with decidable equality. It
takes an actual `IsBlock T` proof and

```text
noStrict : forall C : Finset (List alpha x List alpha),
  not (StrictSystem s C)
```

The forward construction also takes
`{U | ReflTransGen (ChildNC s) T U}.Finite`. It assumes neither a finite
alphabet nor nonerasure, primitivity, irreducibility of the incidence
polynomial, Pisot expansion or strong coincidence. Those conditions may
be needed by a particular supplier of `noStrict`; they are not assumed
by this finite graph argument.

The packet wrappers in
[`NamedFiniteProductivity.lean`](../proof/PscVerif/PscVerif/NamedFiniteProductivity.lean)
take an original `ArchivedPayload.Packet` and its `Valid` proof. The
existing `Packet.no_strictSystem` then supplies exclusion for precisely
`substitution p.fixture`, still one of the two literal substitutions
`1/021/001` and `1/012/001`. Every forward termination wrapper retains
the finite-reachability argument. The swap-seed wrapper discharges only
`IsBlock` from actual seed membership.

### Derivation / reduction

Write `R(T)` for the set of states reachable from `T` by `ChildNC` paths.
Coincidence states are terminal in this relation. Productivity means
that **some** such path reaches a coincidence. Termination with
coincidence is the existing conjunction of finite `R(T)` and productivity
of **every** member of `R(T)`.

Suppose first that a block `T` is nonproductive and `R(T)` is finite.
`factorSet_eq_reachable` identifies its complete factor set with full
`Child` reachability. `reachable_of_not_productive` shows that every
member is noncoincident and is also in `R(T)`. Hence this complete
factor set is finite and coincidence-free. The existing
`strictSystem_of_factorSet` constructs a nonempty actual strict system,
contradicting `noStrict`.

Now let `U` be any member of a finite `R(T)`. Lifting its path to the
complete `Child` relation and applying `Descendants.reachable_isBlock`
proves `IsBlock U`. Path composition gives `R(U) ⊆ R(T)`, so `R(U)` is
finite. The preceding argument makes `U` productive. This handles every
reachable state, including states on branches different from a selected
coincidence path from the root.

The resulting exact statements are

```text
TerminatesWithCoincidence s T iff R(T).Finite
not (Productive s T) implies R(T).Infinite
not (TerminatesWithCoincidence s T) iff R(T).Infinite
```

Each assumes `noStrict` and `IsBlock T`. The first equivalence uses the
finiteness conjunct for its termination-to-finiteness direction; the last is its logical
contrapositive. They assert neither finiteness nor infinitude outright.

The [pre-code source decision](c4-finite-productivity-literature-2026-11-12.md)
records the three primary sources, standard balanced-pair terminology,
the exact implementation contract and the rejected overextensions.

### Evidence and replay

There are nine public theorems in the generic module, including its two
controls, and six named packet wrappers. No exporter or concrete packet
audit protocol is changed. The existing packet theorem and its complete
payload acceptance remain a dependency.

Development compilation with the pinned toolchain and dependencies:

```sh
(cd proof/PscVerif && lake build PscVerif.FiniteProductivity PscVerif.NamedFiniteProductivity)
```

Complete aggregate and compiled transitive-axiom acceptance:

```sh
./tools/check_lean.sh
```

At source construction these new modules have **not yet been compiled**.
The documentation and source inventory are not acceptance receipts.
Any subsequent focused or complete result must be recorded against its
actual source revision and distinguished from the pending parent
acceptance. The full audit permits only the repository's existing
standard axiom allowlist.

The [development evidence packet](../evidence/c4-finite-productivity-2026-11-13/README.md)
preserves the 57-test proof-bank result, source and governance checks,
source hashes, and the focused-build observations. These checks supply
no compiled acceptance for the new modules. The first focused attempt's
object-lookup error is retained alongside the subsequent attempt's
status; neither a pending process nor a queued workflow is a pass.

### Negative controls

`thueMorse_finite_nonproductive` reuses the actual substitution
`0 -> 01, 1 -> 10` and the previously proved strict carrier
`{(01,10),(10,01)}`. It proves in one conjunction that the start is a
block, its actual `ChildNC` reachable set is finite, and it is neither
productive nor terminating with coincidence. Thus deleting `noStrict`
would make the advertised implication false. Thue–Morse is a generic
calibration, not a counterexample in the standing irreducible Pisot scope.

`fibonacci_terminates` supplies a positive control through the new bridge:
the existing exact Fibonacci terminal-child carrier is finite and its
previously proved strict-system exclusion applies. This also preserves
the distinction between terminal-coincidence `ChildNC` closure and full
`Child` closure.

The explicit finiteness argument is the guard against a G1 overclaim.
The infinite-reachability corollaries do not treat a search cap as proof
of infinitude. They also do not turn existential productivity into an
assertion that every possible path eventually hits a coincidence.

### Non-claims / remaining gaps

The named archive contains inverse-overlap ancestors. It is not a finite
forward balanced-pair carrier and cannot discharge the remaining
finiteness premise. An unconditional named termination result needs a
separate source-bound forward-child closure certificate or a theorem
proving that closure finite. The existing `bpaStatesNC_subset` interface
can consume a fully checked carrier containing the actual swap seeds.

No G1, universal C4, pure discrete spectrum, or PSC conclusion is
asserted. All governed claim statuses remain unchanged. Independent
human review remains separate validation debt.

## Next step: check a finite forward carrier

A read-only source review on 2026-11-13, based on
`510239ac0005fb24f880369e55a4b54776224981`, found **no named forward
`ChildNC` carrier certificate** for either `1/021/001` or `1/012/001`.
Their zero-based shared-corpus indices are respectively 86 and 75 in the
[literal identity records](../evidence/rauzy-torus-2026-10-21/corpus.jsonl);
these identity records are not forward certificates.
The existing [BPA census fold](../kernel/psc/parallel_census.mojo) builds
each specimen but retains aggregate counts, maximum size and failure
indices, not each successful specimen's words and complete child rows.
The archived inverse-overlap graphs do not supply those forward rows.

Reuse the canonical [BPA interface](../kernel/psc/bpa.mojo) or its
[bounded builder](../kernel/psc/bounded_bpa.mojo), with exhausted budgets
remaining inconclusive. No new search algorithm or full-corpus census is
needed. The [target-packet preparation](../kernel/psc/target_packets.mojo)
already checks literal ordered factorizations against complete adjacency
rows, and its [reporter](../kernel/psc/target_packet_report.mojo) emits
state words, factor ordinals, child indices, orientations and cut spans.
The existing [archived replay](../kernel/check_target_packets.sh) covers
three different substitutions; it contains neither named carrier. A thin
forward-carrier exporter can reuse this contract without constructing the
additional occurrence-packet graph.

The representation bridge is essential: Mojo's
[`normalise` and `seed_states`](../kernel/substitution_dynamics/balanced_pairs.mojo)
identify a pair with its track swap and start from the three seeds with
`a < b`. Lean's `ChildNC` uses ordered pairs and all six unequal ordered
letter seeds. Export the ordered double cover, or prove the signed
decoding bridge using `Descendants.child_swap`; normalized state indices
alone cannot be passed off as Lean's carrier.

The smallest sufficient formal obligation is a finite decoded carrier
containing every ordered seed and every actual child of each
noncoincident member. Complete decoded row equality should be checked
against `red (subst s T.1) (subst s T.2)`, with empty rows at coincidences,
preserving order, orientation and multiplicity. The existing
[`bpaStatesNC_subset`](../proof/PscVerif/PscVerif/Descendants.lean)
then bounds all seed-generated reachability by that finite set. A
**finite closed superset suffices**: a discovery witness is needed only
to claim that the exported carrier is exactly the reachable set. This
step needs no productivity rank because the present named consumer
already supplies productivity once actual reachability is finite.

Before using such a packet, bind its literal substitution and complete
rows, reject omitted exits and incorrect orientations, and obtain the
required exact-source compiled acceptance. The resulting scope would be
the two seed-generated automata; finiteness from an arbitrary balanced
block would still need its own argument. This review performed no new
enumeration or compilation, supplies no named carrier size, and promotes
neither G1 nor any unconditional named termination claim.
