# Original archived C4 graphs as concrete Lean proof data

This development continues the source-bound refinement merged in #550 at
`06dac7ea4e83a6b5a2c7c36bfe84cfec75da3903`. The
[pre-code gate](c4-archived-payload-import-literature-2026-11-12.md) was committed
before implementation. It preserves the original two substitutions, squared
occurrences and sharp `(16,8)` box. The later `(24,12)` certificate is not an
input to this import.

## Mathematical result and scope

Let `S_f` be the decoded states of the original archive for fixture `f`,
`R` the three original zero-offset roots and `E_f(u)` the original named
geometric overlap. The generic checked-payload theorem states

\[
 u\in\operatorname{orderedLift}(S_f)\ \land\ E_f(u)\ne\varnothing
 \quad\Longleftrightarrow\quad
 \operatorname{Ancestry}(\sigma_f^2,R,u)\ \land\ E_f(u)\ne\varnothing.
\]

`Ancestry` retains every literal inverse step, at any finite depth. The
nonempty restriction is essential: justified residue and box exclusions
may omit empty geometric ancestors.

For a probability additive Haar measure `ν` on the existing original
matrix-adic factor, the checked potential then gives

\[
 (\operatorname{volume}\mathbin{\times}\nu)(E_f(u))=0
 \qquad\text{for every original rooted inverse ancestor }u.
\]

In particular, this holds for the three original roots. The source-specific
finite hypotheses are derived from `packet.Valid`; a concrete generated
`valid` proof must still be kernel checked for each actual archived packet.
The generated `domain_iff`, `roots_null` and `ancestors_null` declarations
then specialize the generic theorem to that packet. Their exact types and
transitive axioms are independently checked after importing the compiled
generated module.

The measure assumption remains explicit. These statements do not identify
the archive with all noncomputable `strictPackets`, assert positive
strict-root measure, prove a strict source-loss witness, or promote C4 or
the general Pisot Substitution Conjecture.

## The unchanged archive

| Fixture | Original substitution | States | Positional slots | Rate | Ordered positions |
| --- | --- | ---: | ---: | ---: | ---: |
| 0 | `1/021/001` | 7,150 | 34,826 | `99/20` | 69,652 |
| 1 | `1/012/001` | 7,083 | 34,853 | `101/20` | 69,706 |

Both rates are below `103/20`, and the existing named algebraic proof gives
`103/20 < beta²`. All positive integer weights, the original state order,
parallel edges, swap bits and discovery addresses are retained. The
historical canonical graph digests remain:

- Fixture 0: `23f85af92c327a64f70983db990753a84cd1489e3c72c3047e51f14e97afce6e`.
- Fixture 1: `a63d544b25b5f7146abbd25f1960fed77f85584a1f20957b5869bea30b389256`.

The authoritative historical construction and receipt remain at
[the November 5 construction](c4-pair-overlap-graph-2026-11-05.md) and
[its receipt](../evidence/c4-pair-overlap-graph-2026-11-05/receipt.json).
The previous [full-address refinement](c4-archived-graph-refinement-2026-11-11.md)
explains the geometric enclosure, matrix-adic exclusions and swapped affine
translation reused here.

## Representation obligations and how they are discharged

| Obligation left explicit in #550 | New proof/data boundary |
| --- | --- |
| Every original selected parent/local pair is enumerated | `NamedArchivedDigits.digitEquiv` is a computable equivalence between `Fin 15` and the actual full `Digit` type for each original squared substitution. |
| Parent, full prefix/suffix and both levels of local address agree | `digit_inflate`, the prefix/letter/suffix identities and `flat_eq_nested_index` authenticate the original `Mark.inflate` construction. |
| Every stored positional slot is an actual inverse occurrence | `SlotValid`, `inverseFromCheck` and `boundSlot_pair` retain both original full marks and the exact raw oriented ancestor. |
| No admitted integral inverse candidate is omitted | `PairComplete` checks all `15 × 15` digit pairs independently of the supplied slot list; `matchingSlot` and `candidatesClosed` transfer this to arbitrary original `SelectedPair` values. |
| Every represented incoming occurrence occurs exactly once | Every stored orientation passes admission; strict address ordering proves row-key injectivity; `row_exact` supplies completeness against the actual incoming occurrence type. |
| Stored states represent distinct track-swap orbits | A checked left inverse of the auxiliary `Lookup.find` at each original state proves `orbitDistinct`. The tree's ordering and injectivity are not assumed. |
| All three roots and every stored state's inverse ancestry are genuine | `rootBound` checks the exact roots; `BirthValid` requires an actual earlier row and positional slot; `tableDiscovery` transfers this to original literal ancestry. |
| The integer inequality uses precisely the geometric rows | `toCertificate` uses the same row lengths and target entries as `tableBinding`; `toCertificate_check` derives acceptance with source-specific numerator and denominator 20. |

### Full literal occurrence enumeration

The squared original parent words have lengths `3,7,5`, giving 15 parent-major
IDs. A digit is a parent together with a complete `Mark`, not a selected
letter or a Parikh vector alone. The inverse map uses the mark's exact
position. Both round trips are proved, so repeated letters at different
positions cannot collapse.

The nested outer/local fields are tied to the original one-step words and
their actual substitution inflation. The theorem preserves the entire
prefix and suffix, then derives the flattened index. A control retains two
different source-0 positions selecting the same letter; another proves that
the same numerical ID can select different letters in the two sources.
Equal incidence matrices therefore do not authorize relabelling the literal
substitutions.

### Complete candidate checks and valid exclusions

For a selected pair with prefix difference `z`, the existing exact decoder
uses

\[
 N(z)=(3z_2-z_1,\ z_0-z_2,\ z_1-z_0),\qquad
 \delta'=N(z)/2.
\]

All three numerator coordinates must be divisible by two. This is the
proved range criterion for the original squared incidence, not the false
requirement that every coordinate of `z` itself be even. The original
matrix-adic range reflection proves emptiness for a failed residue check.

An integral candidate is then tested by the already authenticated strict
rational box predicate. Boundary contact remains admitted. The complete
checker requires a slot for every admitted candidate, including candidates
whose target was not listed in the supplied graph. A supplied slot also has
its own direction, parent/position, residue and oriented-target checks.
Thus omission cannot be hidden by shrinking the stored domain or lowering
the positive-potential sum.

Both orientations of every stored state are checked admitted. This is needed
for `row_exact`: a false exclusion must not conceal an actual incoming edge
between represented states. Track-swap normalization is carried by the
actual `Slot`, so the inherited affine cover uses the correct swapped
translation `current.delta + bottomPrefix`.

### Faithful data and efficient kernel computation

The canonical Mojo exporter emits a balanced `OverlapPacket.Table Nat` and
an auxiliary balanced search tree. Packed rows retain the original state,
positive weight, root/discovery record, depth and ordered list of slots.
The exact field widths are:

| Packed field, low to high | Bits |
| --- | ---: |
| Weight | 20 |
| Degree | 8 |
| State: two letters and three signed coordinates | 25 |
| Earlier parent ID plus one | 14 |
| Earlier slot ID plus one | 8 |
| Depth | 5 |
| Each slot: target, top digit, bottom digit, swap | `14 + 4 + 4 + 1` |

All finite field bounds and unused high bits are checked. Total decoders
use harmless default values for malformed data, but acceptance separately
rejects invalid letters, digits, targets, table layout and noncanonical
payloads. No malformed target is accepted by reducing it modulo the graph
size.

Lookup is logarithmic for the emitted balanced data. Its proof does not
trust the external sort: if two states had the same swap orbit, they would
have the same key and therefore the same checked lookup result, forcing
their IDs equal. The candidate checker uses bounded literal pairs, never a
quadratic scan over all stored states.

`checkRange_append` and `valid_of_range` prove exhaustive composition of
kernel-checked chunks. Each actual leaf chunk is proved with
`decide +kernel`; no `native_decide` axiom, hash assertion, external Boolean
result or noncomputable carrier enumeration supplies the concrete proof.
The generated source is retained in the acceptance artifact.

## Applying the contraction consumer

The existing named geometry supplies compactness, the actual two-step tile
equations, justified exclusions and product-Haar scaling. The literal
cover then gives, on exactly the imported positional table,

\[
 \beta^2 m_i\le\sum_{e\in\mathrm{row}(i)}m_{t(e)},\qquad
 20\sum_{e\in\mathrm{row}(i)}w_{t(e)}\le n_f w_i,
 \quad w_i>0,
\]

where `n_f` is 99 or 101. Repeated targets appear repeatedly in both sums.
The verified strict rate gap feeds `OverlapContraction`'s finite weighted
maximum argument. Neither disjointness of the retained cover pieces nor a
new spectral-radius approximation is assumed. The same accepted data supply
the rooted-domain equivalence and extend nullity to all original finite
inverse ancestors, including empty omitted ones.

## Native, oracle and Lean controls

The canonical native test checks every row and slot of both original graphs
through the new exact packing/decoding boundary. The independent Python
oracle reconstructs the actual source words, all digit addresses, every
candidate, slot, state, weight and discovery witness. It compares the full
original addressed packet, each raw packed row and every auxiliary lookup
node, including the tree shape. Original graph and addressed digests must
also agree.

Negative controls cover omitted repeated positions, direction and swap
changes, the later wrong box, wrong power/source/rate, altered targets,
incomplete or circular inverse ancestry, deletion of a state with all its
stored incident edges, duplicate positional addresses, malformed packed
fields and false lookup identities. The omitted-edge control explicitly
keeps the numerical potential inequality valid while the complete
representation check refuses it.

The Lean controls use actual original roots and literal pairs. Audit
controls additionally reject right-name declarations proving `True` in
place of the required proposition, omitted geometric proof declarations,
incomplete output, wrong fixtures and every transitive axiom outside
`propext`, `Classical.choice`, `Quot.sound`. The allowlist catches fresh
native-reduction axiom names as well as `sorryAx`.

## Replay and acceptance

Canonical native replay:

```sh
cd kernel
pixi run --locked mojo run -I . tests/test_c4_archived_payload.mojo
pixi run --locked mojo build -I . c4_archived_lean_export.mojo -o /tmp/c4-archived-export
/tmp/c4-archived-export packet > /tmp/c4-archived-payload.txt
cd ..
PSC_ARCHIVED_PAYLOAD_NATIVE_OUTPUT=/tmp/c4-archived-payload.txt \
  python -m pytest --assert=plain -q tests/test_c4_archived_payload_oracle.py
python oracles/python/c4_archived_payload.py \
  --native /tmp/c4-archived-payload.txt --controls
```

Complete isolated Lean replay:

```sh
./tools/setup_lean.sh
PATH="$HOME/.elan/bin:$PATH" ./tools/check_lean.sh \
  --archived-packets /tmp/c4-archived-export /tmp/c4-archived-lean
```

The focused workflow checks out the exact PR head, records its commit and
tree, uses the pinned toolchains, performs the complete isolated source build
and compiled bank audit, then checks both generated payloads and their
semantic consumers. Every generated declaration is audited after fresh
import, and Lean's complete emitted payload is independently reconstructed.
Partial or single-fixture development runs do not issue a two-fixture
acceptance verdict.

Exact-revision acceptance and preserved failed attempts belong in the
[companion evidence packet](../evidence/c4-archived-payload-import-2026-11-12/README.md).
Development compilation, native agreement and a generic soundness theorem
are not by themselves acceptance of either concrete archived graph.

## Exact-revision hosted acceptance

Both concrete imports completed at accepted code revision
`249a71b0330401ada5adbff7d9cd280bf0d7530f`, tree
`97b54a6fdccb9a1828be815c2718fbcc5bc67960`.
[Focused run 43175356240, attempt 1, job 131038172377](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43175356240/job/131038172377)
checked out that exact head and completed successfully on November 12 at
09:20:54 UTC. The complete source build finished 9,017 jobs; its compiled
audit checked 6,537 declarations, including 4,774 theorem declarations,
and reached all 2,633 inventoried named proofs. Each complete generated
graph module separately passed its kernel checks, exact semantic-type
checks and all-declaration axiom audit: 1,799 declarations and 776 theorem
declarations per fixture, including generated auxiliary proofs. The only
observed transitive axioms were `propext`, `Classical.choice`, `Quot.sound`.

The actual finite `TableBinding`, candidate closure, roots, discovery and
potential premises are therefore supplied by concrete proof terms for
both original graphs. The domain equivalence and product-Haar nullity
statements above retain their stated geometric scope and measure assumptions.

The 19,222,973-byte
[hosted artifact](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43175356240/artifacts/13929993392)
was downloaded and matched its provider SHA256
`e4e8ed4e5ed77385dbfce4a6b770c4b070fd4e1b2312ef2fa20102b4dfd317d1`.
Artifact inspection verified its revision, source hashes, typed auditors,
full audit logs, original and addressed graph digests, and mutation/refusal
receipts. Both generated sources, both concrete audit logs and the complete
payload are byte-identical to the successful local replay. The canonical
native and Lean payloads have 3,908,423 bytes and SHA256
`447d58d811359235d1f4689433500494ae14724b89b5da91f429e7e7247beaca`.

The [durable acceptance supplement](../evidence/c4-archived-payload-accepted-2026-11-12/README.md)
retains both complete generated sources and their auditors/logs, provider
metadata, the canonical payload, controls and inspection history. Its
later archival commit preserves acceptance of the code revision above;
it is not itself the revision compiled by that earlier run. The archival
change is restricted to evidence and append-only documentation, with
complete tracked-source equivalence checked. Earlier failed development
and inspection records remain historical failures. Independent human
review remains pending.

## Remaining obstruction-to-measure obligation

For `hC : StrictSystem (substitution f) C`, a sufficient next theorem is
to construct a set `Z` in the same original product space with

\[
 Z\subseteq\bigcup_{k:\operatorname{Fin}(3)} E_f(\operatorname{archivedRoot}(k)),
 \qquad 0<(\operatorname{volume}\times\nu)(Z).
\]

The accepted `roots_null` result supplies the nullity premise of
`PscVerif.OverlapContraction.no_positive_subset_of_null`; coverage and
positive measure must still be derived from `hC`. Existing cut-pair
existence/persistence, physical interval interior, nonempty compact overlap,
exact mass balance and zero deficit--overlap products do not supply that
positive product-Haar measure. A proof covering every nonempty
`strictPackets` element by this rooted ancestry would be a separate
extension; the present nullity result does not identify those carriers.

The accepted ancestry statement uses `sigma^2`. A read-only follow-up found
a possible combinatorial extension to one-step root ancestry: each root
has a one-step predecessor among the root orientations (the corresponding
prefixes are both empty, or both `[0]`), so an odd root path could be padded
and consecutive edges grouped using `Mark.inflate` and `residual_inflate`.
The required composition/parity/root-padding lemmas have not been
formalized or audited. Exponent-one Haar scaling alone would not justify
direct propagation for these tiles: the named tile equations currently
provided are `tileEquation_two` and `tileEquation_even`.
