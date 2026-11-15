# C4: bind literal inverse rows and derive the overlap-set union

Date: 2026-11-10. This continuation reconciles historical
[PR #497](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/497)
at `0f4b9a05ce95e59d9b6cde11fcdf22d161375030` with accepted
`main@8c04ec85e12d9370481a493bb2c8f822cbb81a2d` (PR #537).
The [targeted stop/go](c4-literal-inverse-binding-literature-2026-11-10.md)
preceded implementation. Historical source files and evidence pins are
preserved. No governed claim status changes.

## 1. What this step supplies

The old inverse adjacency rows retain repeated targets, but do not serialize
the two literal incoming marks or the orientation used when normalizing a
target. The new canonical adapter reconstructs these identities and checks
them against a separately enumerated ordered forward inventory. A new Lean
interface derives ancestry and count transport from exact positional rows
and earlier-state discovery witnesses. A second Lean module derives the
complete overlap-set union from the original tile equations.

These are three different verification scopes:

| Layer | What is established | What is still supplied separately |
| --- | --- | --- |
| Canonical Mojo plus independent Python | Every literal row slot, its orientation, both ordered lifts, internal completeness and discovery witnesses for the twelve recorded sources | Compact interpretation and soundness of pruning outside that finite domain |
| `OccurrenceGraphBinding` | Actual positions construct inverse marks; positional completeness constructs a count equivalence; earlier-state witnesses construct ancestry; exact canonical IDs identify swap orbits | The entire serialized twelve-source packet is not evaluated as a closed Lean term |
| `OccurrencePiece` | Full inverse overlap union, nonintegral-piece emptiness and normalization translations follow from original tile unions and explicit additive-space hypotheses | Construction of the compact matrix-adic space and tiles, range reflection in that space, finite pruned cover, Haar measure and positive root measure |

The complete geometric finite-graph instance remains open. This package does
not infer that instance from matching adjacency counts.

## 2. Literal source and serialized records

The twelve substitutions are
`11/{012,021,102,120,201,210}/{01,10}`. Their common incidence and actual
two-step incidence are

\[
M=\begin{pmatrix}0&1&1\\2&1&1\\0&1&0\end{pmatrix},
\qquad
M^2=\begin{pmatrix}2&2&1\\2&4&3\\2&1&1\end{pmatrix},
\qquad \det(M^2)=4.
\]

Each source has exactly 18 positions across its three actual two-step image
words. A digit record is

```text
digit source digitId selectedLetter sourceLetter position prefix0 prefix1 prefix2
```

For inverse source `p=(a,b,z)` and incoming marks
`sigma²(A)=P a S`, `sigma²(B)=Q b T`, solve

\[
M^2y=z+\pi(Q)-\pi(P).
\]

The raw ancestor is `u=(A,B,y)`. The original canonicalization stores
`min(u,swap(u))`; the adapter additionally retains which orientation occurred:

```text
edge source row slot target topDigit bottomDigit targetSwapped
birth source target earlierRow earlierSlot
```

Root births are `-1 -1`. The three canonical roots per source are the
zero-offset pairs `(0,1)`, `(0,2)`, `(1,2)`; their ordered lift contains both
orientations. All nonroot witnesses identify an actual earlier row and its
exact occurrence slot. A circle of references cannot substitute for ancestry.

The format starts with `schema c4-literal-inverse-binding-v1` and includes
every literal image, iterated word, digit, state, occurrence slot and birth,
followed by checked source summaries and a final total. In each source block
all three images precede all three iterated words. The complete verifier
rejects missing, duplicated, extra or changed records.

## 3. Internal completeness is checked in both directions

The new adapter leaves the old graph constructor unchanged. On its supplied
state domain it enumerates every incoming digit pair, solves the integral
equation exactly, and retains the pair precisely when the normalized raw
ancestor belongs to the represented domain. **This internal comparison uses
neither the stable-box filter nor the carrier filter.** The resulting ordered
target sequence must reproduce every historical adjacency slot.

The second scan runs in the forward direction on both orientations of every
represented state. For every pair of actual positions it computes

\[
z=M^2y+\pi(P)-\pi(Q)
\]

and retains the edge exactly when the child is represented. It compares full
edge identities with the lifted incoming slots: source packet, both local
positions and target packet. Equal endpoint IDs alone do not identify an edge.
The same independent scan checks the count transpose.

Mojo uses checked integer arithmetic, bounded injective integer keys and
the exact adjugate equation, followed by multiplication back into the
original equation. Python independently rescans literal word prefixes and
derives its inverse by `Fraction` Gaussian elimination. The historical
independent graph snapshot is frozen before caching. Public acceptance uses
explicit exceptions and remains active under `python -O`.

The finite domain is explicit: twelve sources, operational state cap 20,000
per source, at most 81 row slots, 18 incoming digits, and coordinate key bound
64. A represented state outside the key bound is refused. A forward candidate
outside that bound cannot belong to the already validated finite domain;
skipping it is not a geometric emptiness claim. Exhausted budgets refuse a
conclusion.

The observed native/oracle inventories agree:

| Quantity | Total |
| --- | ---: |
| Canonical states | 43,915 |
| Ordered states | 87,830 |
| Canonical inverse occurrence slots | 253,395 |
| Ordered positional edges | 506,790 |
| Targets normalized by swapping | 118,583 |
| Repeated-target slots beyond the first occurrence of a target in its row | 24,583 |
| Nonroot earlier-state birth witnesses | 43,879 |

The expected complete packet contains 8,406,642 bytes. Its digest, checked
against canonical stdout during acceptance, is
`9980da2a7c4cf049deff84a607f774dccd7c062f1eb457174138bac987268575`.

## 4. Lean binding of rows, discoveries and exact orbit IDs

`OccurrenceGraphBinding.Slot` retains a normalization bit, two valid local
indices, and the exact forward packet equality. It constructs the existing
`InverseOccurrence` and proves that both positions and prefixes are preserved.
The ordered lift is the union of supplied representatives and their swaps.

`Row.Exact` requires injectivity and surjectivity on actual positional
identities. From these properties the module constructs an equivalence with
the complete incoming edge type, then identifies row counts with
`packetInverse`. It does not assume uniform degrees.

`Discovery` requires each state to be a root or have an actual occurrence from
a strictly earlier state. Strong induction constructs its inverse ancestry.
When normalization swaps a raw target, the proof swaps the complete existing
ancestry path using the swap-closed root set. It does not merely rename the
last packet. The existing `ancestry_packet_transpose` then applies with its
unchanged positive-length, positive-scale and exact image-scaling hypotheses.

The canonical-ID interface additionally requires exact orbit uniqueness of
the serialized representatives. It proves an equivalence between those IDs
and actual swap-orbit labels. `table_matrixEntry_transpose` consequently
identifies each raw repeated-target matrix entry with its forward transpose.
The new module has 33 named theorem declarations. These are generic kernel
proofs of the interface, separately from the executable full packet receipt.

## 5. The geometric union now follows from the original tile equations

Let `G` be an additive commutative group, `A : G →+ G` its internal action,
`star : Z³ →+ G` the integral translation map, and `K_a` the supplied tiles.
Define

\[
E(a,b,z)=K_a\cap(K_b+\star z).
\]

`OccurrencePiece` proves that track swap changes this set by translation:

\[
E(\operatorname{swap}(p))=E(p)-\star(p.\delta).
\]

For an actual inverse occurrence with prefixes `P,Q`, injectivity of `A` and
the commutation law `A(star y)=star(M y)` give the exact paired-piece identity

\[
\bigl(AK_A+\star\pi(P)\bigr)\cap
\bigl(AK_B+\star(z+\pi(Q))\bigr)
=A E(A,B,y)+\star\pi(P).
\]

If the stored ancestor is the swap of `(A,B,y)`, its translation changes to
`star(z+pi(Q))`. Retaining only the original top prefix would give the wrong
piece. `pairedPiece_eq_stored_slot` connects this law directly to the
new normalized occurrence record.

The complete union theorem additionally takes two explicit geometric inputs:

1. `TileEquation`: each `K_a` is exactly the union of the affine images indexed
   by all actual incoming literal marks.
2. `ReflectsIntegralRange`: whenever `star(v)` has an ambient preimage under
   `A`, the integral vector `v` has an integral preimage under `M`.

Expanding the two original tile unions produces a pair of marks for every
point of `E(p)`. Their difference lies in the range of `A`; range reflection
supplies the integral ancestor. The paired-piece identity therefore gives

\[
E(p)=\bigcup_u\ \bigcup_{e:\operatorname{InverseOccurrence}(s,p,u)}
\left(AE(u)+\star\pi(P_e)\right).
\]

The overlap cover is derived, not assumed. The module also proves that a
nonintegral candidate pair has empty intersection under the same range
reflection premise. All thirteen named proofs are set identities or their
algebraic prerequisites; no topology or measure is needed for them.

**Range reflection has a specific intended ambient space.** It is appropriate
to the compact matrix-adic factor `H_M` of the repository's
[M-adic bridge](c4-nonunit-madic-counting-bridge-2026-11-04.md). It generally
fails on the unrestricted noncompact product of completion fields, where
multiplication by a nonzero algebraic number is surjective. Constructing the
compact factor and proving its range criterion remains a required instance.

The displayed union ranges over **all integral ancestors**. Restricting it
to the finite historical graph still needs sound stable-box/carrier
exclusions and a complete finite-domain binding of the geometric pieces.

## 6. Controls and replay

The native regression rejects altered words, prefixes, selected letters,
indices, orientation bits, targets, repeated slots, state identities and
birth references. It retains exact nonintegral rejection, original-equation
verification and exhausted-budget controls. The independent suite includes a
mutation that substitutes a second occurrence with the same target: every
old adjacency ID and row count remains unchanged, while the positional
certificate is rejected.

The new independent Quint model exhausts 2,304 actual occurrences across
sixteen binary constant-length-two substitutions, a six-slot repeated-target
inventory and eight oriented three-state discovery trees. Nine tests cover
normalization round trips, exchange of both indices, translation correction,
positional inventory and rooted ancestry. Seven source-bound mutations must
reach their named failing assertions; a parse failure or missing test does
not count as a successful rejection. These are bounded controls, not the
twelve-source certificate.

```sh
python tools/make_proof_bank.py --check
./tools/check_lean.sh
python tools/check_c4_literal_inverse_binding_quint.py --output /tmp/literal-quint
cd kernel
pixi run --locked mojo run -I . tests/test_c4_literal_inverse_binding.mojo
pixi run --locked mojo run -I . c4_literal_inverse_binding.mojo > /tmp/literal-native.txt
cd ..
PSC_LITERAL_INVERSE_NATIVE_OUTPUT=/tmp/literal-native.txt python -m pytest --assert=plain -o addopts='' -q tests/test_c4_literal_inverse_binding_oracle.py
python oracles/python/c4_literal_inverse_binding.py --native /tmp/literal-native.txt
```

The dedicated workflow records exact head, tree, source hashes and complete
native output, refuses tracked source drift after execution, and uploads the
independent receipt. Its separate Quint job records all nine tests and seven
mutations. The existing isolated whole-bank Lean/axiom workflow is the
production-import acceptance gate. Development compilation with reduced
imports is not a replacement for that fresh build. Exact published-revision
receipts and any pending jobs are recorded in PR #497 after observation.

## 7. Remaining proof obligations

The next geometric instance must construct the compact matrix-adic action
and integral range reflection; bind the actual compact prefix tiles to the
original tile equation; and justify every exclusion when restricting the
all-ancestor union to the finite graph. Product-Haar scaling and the
within-letter measure-disjointness needed for an equality recurrence remain
separate from the present set identity. A represented strict-cut root must
still be shown to have positive compact measure.

The historical finite SCC/weight certificates and written geometric
derivations retain their original scope. This continuation does not turn
them into a closed Lean instance or enlarge their twelve-source coverage.
The inverse-closed/forward-leaking control from #537 remains valid. Positive
physical interval mass alone supplies no compact-measure conclusion.
C4, Concentration, global G1 and PSC remain open. Independent human review
remains final validation debt and does not block mechanically accepted
research progression.
