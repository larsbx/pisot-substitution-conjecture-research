# Ordered forward closure for the C4 parameter family

Let `σ_k = (1, 0 1^k 2, 001)`, with seed `(01,10)` and the repository's
literal `ChildNC` relation. The following is a family-specific closure
certificate. Every child listed in a row is an actual irreducible factor
occurrence, in order. Diagonal targets are included and are terminal.

## Derivation

For `k ≥ 5`, set `n = k - 5`. The certificate has 25 rows for representative
word pairs, with another slot for each track swap. The two ordered diagonal
pairs occupy duplicate slots. Each word is a concatenation of fixed strings
and runs `1^(n+5)`. The state list includes `(01,10)` in its original order.

For irreducibility, align both tracks by letter runs; the length of each aligned
span is an affine expression in `n`. Every unequal-letter span has constant
length. On an equal-letter span the Parikh difference is constant. The
symbolic replay checks that no positive proper prefix has zero difference,
and that the final difference is zero. The equal-`1` spans in row 7 can
shrink to zero at `k=5`, with the same nonzero difference on either side.
Singleton diagonal words have their only positive cut at their endpoint.

For the complete inflation rows, write `A = 0 1^k 2`. Besides literal children and
repeated diagonals, the table contains repetitions of the period consisting of
`k-2` diagonal `(1,1)` occurrences followed by `(1120,2011)` or its track swap.
After the last period there are another `k-2` diagonal occurrences. The next
literal child supplies the terminal phase, `112` on the long track and `2`
on the short one. The identity `(xy)^m x = x(yx)^m` applies with

| Track | x | y | yx |
| --- | --- | --- | --- |
| Long | `1^(k-2)112` | `0` | `A` |
| Short | `1^(k-2)2` | `011` | `A` |

The common period is therefore represented by the exact track words of the
child occurrences. Affine repetition counts determine how many copies of
`A` each track contributes. For each representative row the symbolic
replay compares both resulting concatenations with literal substitution
of the parent. Adding the track swaps preserves the order of occurrences.
The repository's `red_unique` identifies any factorization satisfying
these two concatenations and irreducibility with the actual reduction.

For `k=2,3,4` the proof can use finite literal carriers. The canonical Mojo
engine built a closed carrier and checked every actual ordered child,
then restricted to `(01,10)`. An independent literal Parikh-prefix reduction
agreed on every reported count. It also checked productivity directly.
Every noncoincident block has a path of length at most two to coincidence
for `k=2`, and an immediate coincidence child for `k=3,4`. For `k≥5` every
symbolic noncoincident row explicitly contains a singleton diagonal child
for every parameter. This proves the stronger one-step productivity statement
on the unbounded range. Tracks swapped in either orientation retain that exit.

| k | Reachable ordered states | Longest track | Ordered child occurrences |
| --- | ---: | ---: | ---: |
| 2 | 128 | 53 | 954 |
| 3 | 60 | 22 | 638 |
| 4 | 48 | 26 | 830 |
| 5 | 48 | 29 | 1,298 |
| 8 | 48 | 38 | 3,446 |
| 16 | 48 | 62 | 14,630 |
| 30 | 48 | 104 | 53,298 |
| 64 | 48 | 206 | 248,390 |
| 137 | 48 | 425 | 1,151,546 |

## Negative controls

- At `k=3`, the reachable parent `01110111201112 / 11120111200111`
  has child `12101112011120111200 / 20011011120111201112`, outside the 25
  representative templates and their swaps instantiated at `k=3`.
- Starting the same affine alignment at `k=4` changes the order of run
  endpoints in row 7, although the 48 literal states still close there.
  The symbolic scan starts at `k=5` and uses a literal control for `k=4`.
- A fixed word-length cap cannot prove this theorem. For example, the first
  two reductions already reach `(1^k2001,0101^k2)`, of length `k+4`.
- The seed and its swap have a two-cycle, and the row also contains diagonal
  exits. Termination with coincidence requires an available path to a
  diagonal from each reached state.

## Prior coverage and conjugacy

The [pre-code family screen](c4-parameter-family-stop-go-2026-11-14.md)
documents the trace-at-most-two result of
[Akiyama, Gähler and Lee, Proposition 2.2](https://dmtcs.episciences.org/2089/pdf),
which covers `k=1,2`. Barge's
[endpoint theorem](https://arxiv.org/html/1403.7826v2) requires another
endpoint profile, and his [β-substitution theorem](https://arxiv.org/html/1505.04408v2)
applies to the β-substitution itself. The shared cubic, one-step word
morphisms, positive powers under relabelling or reversal, and common-word
rotation were screened. The one-step nonerasing obstructions are in the
pre-code review. The endpoint screen here extends to equal positive powers.
For a literal nonerasing intertwiner from `σ_k^m` to `ψ_k^m`, the last-letter
maps force `3 | m`, since the `σ` endpoint has period dividing two and the
`ψ` endpoint is a three-cycle when `3 ∤ m`. In the reverse direction, the
first-letter maps force `2 | m`, since the constant `ψ` endpoint must map
to a fixed point of the powered `σ` endpoint. Consequently an equal-power
pair of nonerasing intertwiners can only occur at multiples of six. This
is a necessary endpoint condition. General dynamical conjugacy, including
return recodings and shifted intertwiners of powers, remains open. No all-parameter published
identification was found in this search.

The finite carrier and direct productivity prove termination with coincidence.
Expanding a singleton coincidence produces only singleton coincidences, so
passing from terminal `ChildNC` to the full reduction does not add new
noncoincident states and adds at most the three diagonal letter pairs.
The existing strong-coincidence witnesses for every `k ≥ 2` also give
termination through the repository's finite-productivity implication.
The spectral corollary uses the primitive irreducible Pisot arithmetic in the
pre-code note and [Barge, Štimac and Williams, Corollary 2](https://web.math.pmf.unizg.hr/~sonja/PDSfinal.pdf).
These are the family-specific mathematical deductions from the executable
certificate and the published bridge. Formal acceptance and the independent
named archive pipeline have their own evidence.

## Reproduce

From the repository root:

```sh
python3 oracles/python/c4_parameter_family_carrier.py
cd kernel
pixi run mojo run -I . tests/test_c4_parameter_family_carrier.mojo
```

The replay also rejects three alterations of the seed row that
omit its diagonal occurrences, reorder the children, or change a track
orientation, and checks the six possible endpoint-power residues.

The Mojo control uses limits of 250 normalized states and 2,000 letters per
state. A refused construction exits with an error. The symbolic replay uses
integer affine rules for the word and row identities, without a parameter
or word-length cap.

## Formal termination theorem

The family now belongs to the governed `PscVerif` library. The earlier
standalone word proof has moved to
[`C4ParameterFamilyWords.lean`](../proof/PscVerif/PscVerif/C4ParameterFamilyWords.lean).
Its former `proof/psc_routes/` location was outside the full-library audit;
earlier broad green CI did not by itself establish its hosted compilation.

[`C4ParameterFamilyCarrier.lean`](../proof/PscVerif/PscVerif/C4ParameterFamilyCarrier.lean)
supplies the remaining deductions. Its public endpoints are:

```lean
Psc.ParameterFamily.finite_and_productive
Psc.ParameterFamily.coincidence_child
Psc.ParameterFamily.terminates_with_coincidence
```

For every natural parameter `k >= 2`, the literal ordered seed `01/10`
has finitely many reachable states under the repository's actual `ChildNC`
relation, and every reached state has a path to coincidence. The final
endpoint has the existing `Psc.StrictSystem.TerminatesWithCoincidence`
type. For `k >= 3`, every reached noncoincident state has an immediate
coincidence child. No supplied finiteness, strong-coincidence, strict-exclusion
or original-archive premise enters these endpoints.

The existing `Productive` and `TerminatesWithCoincidence` definitions are
extracted unchanged into
[`Termination.lean`](../proof/PscVerif/PscVerif/Termination.lean).
Their names, implicit parameters and bodies are preserved; `StrictSystem`
imports them. This keeps the family consumer's dependency closure within
the needed combinatorial library while the full audit still verifies every
existing spectral consumer.

For the symbolic range `k=n+5`, an aligned-run proof establishes `IsBlock`
for every decoded state. In the arbitrarily long equal-`1` spans, the
prefix-count difference is a fixed nonzero vector; finite unequal-letter
segments are checked exactly. The earlier two-track identities and
`red_unique` then identify each complete listed row with actual reduction.
Track swaps preserve occurrence order. Closure embeds every reachable
state into the image of `Fin 50`, sufficient for finiteness; this formal
upper carrier does not assert an exact reachable cardinality of 48.

For `k=2,3,4`, literal tables contain respectively 128, 60 and 48 ordered
states. Kernel evaluation checks each state's irreducibility, both inflated
track concatenations, bounded child indices, and an actual child with a
strictly smaller natural rank. Well-founded induction gives productivity.
The checks for `k=3,4` additionally require that chosen child to be diagonal.
All finite decisions use Lean kernel reduction, without native evaluation
axioms.

### The immediate-exit threshold is sharp

[`C4ParameterFamilyControls.lean`](../proof/PscVerif/PscVerif/C4ParameterFamilyControls.lean)
checks a seven-edge literal path at `k=2` from `01/10` to
`010112/200111`. That state's complete reduction consists only of
`10112101120112001/00111011201120112`, another noncoincident state.
Thus extending the immediate-exit conclusion to all `k>=2` would be false.
The available multi-step coincidence path at this boundary is retained.

### Reproduce formal acceptance

```sh
./tools/setup_lean.sh
./tools/check_c4_parameter_family.sh
./tools/check_lean.sh
```

The focused family gate copies source and pinned configuration into a fresh
workspace, downloads dependency artifacts from the fixed upstream source-hash
cache, recompiles the complete family dependency closure, and checks the
public endpoint types against an independently written literal substitution
and ordered seed. Missing declarations and wrong theorem types are refused.
The only permitted transitive axioms are `propext`, `Classical.choice` and
`Quot.sound`. The unchanged full-library gate separately inventories and
audits every project declaration, including all new family proofs and controls.

The [family evidence packet](../evidence/c4-family-termination-2026-11-14/README.md)
records the local compilation scope and source hashes. Hosted results must
be read at their producing revision. The canonical Mojo samples and
independent Python symbolic replay remain corroborating checks; the universal
quantifier is discharged by the Lean deduction.

The family extends PR #570 at `dcfbef0808e3c5fc058a1e0c4f78c7f410630fde`,
which includes #571's word identities and independent replay.
The named archive's nine-endpoint replay has its own
[successful run 43570948106](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43570948106)
at source revision `8a6bd5732fefba94ad4fef5df2333065c1302452`.
The primitive, irreducible Pisot arithmetic and the published spectral
implication are documented mathematical arguments, not new Lean endpoints
in this increment. Universal A1′, BH, C4, G1 and PSC are outside the family result.
