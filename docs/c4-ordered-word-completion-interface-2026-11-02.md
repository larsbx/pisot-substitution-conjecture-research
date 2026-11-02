# C4 ordered-word completion interface — 2026-11-02

**Status:** research contract and elementary finite-graph separation, **not a C4 proof**.
**Read baseline:** `main@f76df185c25542f721d6041826cafdb9a0d3bed1` (merged PR #448).
**Canonical tracking:** [closed issue #9](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/9) is research routing, not theorem completion; universal [A1′ #138](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/138), [BH #139](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/139), and [#84](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/84) remain open.

## 1. Precisely which finite object is being studied

Let `sigma` be a primitive irreducible Pisot substitution on three letters.
**Conditionally supply** a nonempty, finite, strict child-closed component
`C` of *actual irreducible balanced pairs* with its complete ordered,
occurrence-indexed factorization. Strict means the component has no
coincidence descendants. Do not assume that every global nonproductive
failure produces `C`: this is the separate G1 extraction/termination gap.

For an oriented state `T=(u,v)`, every output cut `t` of
`(sigma(u),sigma(v))` has its **actual** (possibly asynchronous) source
indices `i,j`, within-image indices `r,s`, and prefix defect

```text
D_sigma(T)(t) = M [Parikh(u[:i]) - Parikh(v[:j])]
                + Parikh(sigma(u[i])[:r])
                - Parikh(sigma(v[j])[:s]).
```

The terminal-image convention is understood. Zero returns determine actual
balanced-child boundaries; their order cannot be quotiented away. This law
and bounded return gaps are *already proved* in
[c4-prefix-difference-return-calculus.md](c4-prefix-difference-return-calculus.md).
Multi-level legal ancestry, finite hierarchy offsets and legal-cut extraction
are likewise established *interfaces*, not the missing coupling theorem.

A target-aware packet in the existing canonical diagnostic records the
normalized BPA state, physical orientation, selected current occurrences,
both inherited/full occurrence addresses, intended target letters, exact
residual Parikh vector, interior/boundary flag, and incoming *ordered*
parent/ordinal/child factor edge. Its affine residual transport is

```text
r_next = M r_now
         + Parikh(sigma(top_letter)[:digit_top])
         - Parikh(sigma(bottom_letter)[:digit_bottom]).
```

An occurrence survives an edge only when **both** selected occurrences
belong to the *same* actual child; split descendants are discarded and
counted. The graph is not the graph of all simultaneous legal-cut ancestries.
Do not conflate its packet SCCs with strict child-closed BPA SCCs. Source:
[target-aware BPA diagnostic](target-aware-bpa-diagnostic-2026-10-02.md).

## 2. Barge–Diamond candidate and the unproved ordered-word implication

For each candidate unordered good edge `G`, the
[candidate-edge bridge](c4-good-edge-system-bridge.md) checks all actual
first pairs and first-child occurrences against the prefix selector and
physical hub residual. The **genuine** Barge–Diamond edge survives on a
strict PIP component, so the mask is nonempty; a singleton mask forces
the *identity* of the candidate good edge. These statements are necessary
conditions, not proof of eventual coincidence of an arbitrary surviving edge.

The missing **word-level** implication needs a quantified statement such as:

> For every actual strict child-closed `C` as above, find a literal interior
> zero-return/newborn child boundary in some finite inflation, with recorded
> ordered factorization and legal occurrence ancestry, whose right-adjacent
> pair is in `Sync_+` or whose left-adjacent pair is in `Sync_-`.

That is the [issue #9 C4 target](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/9).
To derive it from the endpoint candidate mask, a *new* lemma must
constrain the **entire ordered hub-residual word**, including its interior
children and sign/orientation lifts. Extending a constant first-child phase
to all children by fiat is invalid. A finite candidate mask is neither that
lemma nor a global strict-component extraction theorem.

A packet's **immediate diagonal** target and eventual synchronization
`Sync_±` are different predicates. A valid C4 argument must explicitly
prove the bridge from whichever local packet target it uses to the
eventual right/left adjacent synchronization asserted by C4.

## 3. Finite-graph logic: existential hitting vs forced avoidance exclusion

For a *complete* finite packet graph `P=(V,E)`, an indicated set of
successful packets `H`, initial roots `R`, and terminal nonsuccess
packets `F`, consider only the actual transitions in `E`.

**Elementary finite-graph lemma (conditional on that complete graph).**

1. Every root has **some** path to `H` iff every root is in the reverse
   reachability set of `H`.
2. Every maximal root-started trajectory in the *retained graph* hits
   `H` iff no root-reachable subgraph of `V\H` contains either
   a directed cycle or a dead-end nonsuccess terminal.

The second equivalence includes both finite maximal paths and infinite
ones. Proof: a reachable non-target cycle yields an infinite avoiding
walk, and a reachable nonsuccess dead end yields a finite avoiding maximal
walk. Conversely, any infinite avoiding walk in a finite graph repeats a
vertex, and any finite maximal avoiding walk ends at a dead end. QED.

**Scope firewall:** this is elementary finite graph theory, not a
PIP/C4 theorem. A capped or incomplete graph cannot be called complete;
the packet builder intentionally omits split descendants. Even a full
certificate of item (1) is not item (2), and **C4 need not require item
(2)**. A proposed universal C4 proof must identify the exact selector/
coverage rule it needs, rather than replace its existential target by a
stronger unproved all-packets hitting assumption.

## 4. Golden controls, with the correct rejection layer

- Real-secondary PIP `0->1, 1->02, 2->202`: the four target-free
  packet SCCs have exits, while source SCCs have successful target paths.
  Packet cycle `209 --396--> 429 --820--> 209` has physical offsets
  `0 -> 1 -> 0`, residuals `(-1,1,0)` and `(1,-1,1)`,
  and actual ordered factor ordinals `2,0`.
  It refutes blanket physical-offset monotonicity or
  eventual permanent alignment for arbitrary retained packet lineages.
  It **does not** refute a correctly restricted strict child-closed
  PIP theorem: this PIP source support is productive.
- Primitive non-Pisot strict `1->2, 2->123, 3->2`:
  constant defined hub phase and bounded return gaps coexist with a
  strict nonproductive component. Rejection must use the missing Pisot/
  synchronization hypothesis, not erase its literal factor edges.
- Actual G/F `1/2/021`: synthetic `1,1,3` child counts are false;
  literal lengths are `1,2,5`, with a diagonal `2/2`.
  The control deliberately survives early algebraic and endpoint tests
  and fails at ordered word factorization.
- PIP default swap `01/10` has target depth two, not depth one;
  its inflated first level has no interior zero return.
  Matching letters at a nonzero residual are not successes.
- Undefined hub bits for diagonal or no-hub children must remain
  *undefined*, never silently coerced to phase zero/one.

Original independent receipts and replay commands:
[ordered-hub negative](c4-ordered-hub-offset-negative-2026-10-06.md),
[target-aware diagnostic](target-aware-bpa-diagnostic-2026-10-02.md),
`kernel/check_target_packets.sh`, `kernel/check_ordered_hub.sh`,
`evidence/target-aware-bpa-2026-10-02/` and
`evidence/ordered-hub-packets-2026-10-06/`.
These are historical reported exact replays; this note does not claim
to have rerun the Mojo compiler or CI.

## 5. Next falsifiable proof/check packets, in priority order

1. **Strict-component word selector.** Input an actual finite strict
   child-closed component with complete ordered children, endpoint
   candidate mask and full hub words. Seek a theorem valid for
   *arbitrary component size* that forces an interior `Sync_±` cut.
   Accept a literal, fully occurrence-indexed proof (not a
   quotient-only parity assertion), or a replayable counterexample
   to the precise proposed intermediate lemma. Reuse the preexisting
   first-child selector and packet/offset kernels; no new sieve of
   three-state SCCs.
2. **Legal-cut/supertile coupling.** Explicitly track source
   supertile-boundary flags on both sides, actual within-image
   offsets, oriented child ordinal, and a legal hull context through
   multiple ancestry levels. Prove why the two flags *must*
   eventually synchronize under the strict PIP hypothesis, or give
   a counterexample. Repetition and local legality alone are already
   known insufficient (Tribonacci productive germ, non-Pisot strict
   germ); do not reimplement those controls.
3. **Coverage choice.** State whether the proposed C4 argument uses
   one existential selected lineage or exclusion of every avoiding
   cycle. Check root coverage, split/terminal miss accounting and
   full child closure *before* any graph-theoretic certificate.
4. **Separate G1 route.** Universal extraction of a finite strict
   component requires G1b-2/renewal termination or an independently
   proved alternative. No C4 lemma may assert its own premise.
5. **Assumption review.** Reject any silent independence/global
   unimodularity, predecessor-contraction, unproved native-to-Lean
   refinement, or finite-census-to-uniform transfer.

**Acceptance boundary:** a correct scoped graph certificate or
a refuted candidate lemma is useful progress. Neither changes the
governed status of C4, BH #139, A1′ #138, G1, PDS or PSC.
