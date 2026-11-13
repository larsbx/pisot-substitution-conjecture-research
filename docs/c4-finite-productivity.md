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
