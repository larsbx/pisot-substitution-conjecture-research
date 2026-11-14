# C4 parameter family termination — source and acceptance

This increment extends `dcfbef0808e3c5fc058a1e0c4f78c7f410630fde`
(#570, containing the merged #571 word identities). It adds an actual
`ChildNC` closure/productivity proof and moves the family into the governed
`PscVerif` import and audit closure.

## Exact theorem scope

The literal substitution is `0 -> 1`, `1 -> 0 1^k 2`, `2 -> 001`.
The ordered starting pair is `([0,1],[1,0])`.

- `Psc.ParameterFamily.finite_and_productive`: for every `k>=2`, the actual
  reachable set is finite and each reached state has a coincidence-reaching
  path.
- `Psc.ParameterFamily.coincidence_child`: for every `k>=3`, each reached
  noncoincident state has a diagonal immediate child.
- `Psc.ParameterFamily.terminates_with_coincidence`: the first result expressed
  with the existing `Psc.StrictSystem.TerminatesWithCoincidence` predicate.

The public endpoints require no caller-provided carrier, closure, productivity,
strong coincidence or archive premise. At `k>=5`, 25 symbolic representative
rows and their track swaps supply a 50-slot finite upper carrier. Literal
boundary tables cover `k=2,3,4` and kernel-checked descending ranks supply
productive paths. No native-evaluation axiom is used.

The detailed reconstruction, prefix scan, reduction uniqueness and boundary
argument are in [the family note](../../docs/c4-parameter-family-carrier-2026-11-14.md).

## Publication-time verification status

The initial publication is a draft while the complete Carrier module and its
fresh endpoint audit finish compilation. Local pinned Lean 4.34.0-rc2
compilation has passed for the word identities and negative-control module.
These development runs reuse existing dependency objects and are not the
source-isolated acceptance gate. The source hashes and retained local logs
identify their scope.

The canonical Mojo sample replay passes at
`k=2,3,4,5,8,16,30,64,137`. The independent Python symbolic replay passes for
all `k=n+5` through affine identities, with literal boundary checks at
`k=2,3,4` and three row-mutation refusals. The 57 proof-bank tests pass.
These checks do not substitute for compilation of the universal theorem.

The new [focused workflow](../../.github/workflows/c4-parameter-family.yml)
requires a fresh source/configuration workspace, pinned upstream dependency
sources/cache, complete family dependency compilation, three independently
literal endpoint types, and six wrong-type/missing-name controls. It audits
all compiled constants owned by the three family modules and the extracted
shared `Termination` module, including private and generated declarations.
The only allowed axioms are `propext`,
`Classical.choice` and `Quot.sound`. The unchanged full-library workflow also
builds and audits the new modules through `PscVerif.lean`.

Local access to the upstream Mathlib artifact cache returned HTTP 403, so
the fresh hosted workflow is required for source-isolated acceptance.
Hosted results belong to the revision that produced them and should be read
from the PR checks; none is assigned to this source before completion.

## Negative controls

The new Lean control supplies a seven-edge path under actual `ChildNC` at
`k=2` from the ordered seed to `010112/200111`. Its complete ordered child
row is the singleton
`[10112101120112001/00111011201120112]`, with unequal tracks. Thus the stronger
immediate-coincidence assertion at every `k>=2` is false at a reachable state.

The endpoint audit separately rejects a harmless `True` theorem and an absent
declaration for each required semantic type. Existing canonical forward-carrier
tests cover omitted, reordered and duplicated children, altered orientation,
out-of-range indices, missing seeds and budget refusal. Their contract and
the family sampling contract remain distinct.

The first local control attempt tried to decide `ChildNC` directly, which has
no decision instance. The successful control uses the proved streaming
`IsBlock` checker plus complete literal rows and `red_unique`; it does not
add a decision axiom. A separate concurrent/default-thread local attempt was
cancelled without a mathematical result; the same source passed with bounded
compiler concurrency. The retained transcripts preserve these scopes.

## Accepted dependency and non-claims

The [integration run snapshot](integration-run-snapshot.json) records four
successful gates at `251079fc55c1fa7f6a9d3392e612c7e63132eefc`: full Lean,
original nine-endpoint archive replay, native forward carriers and broad
research checks. Those results certify the prior named chain, not the new
parameter-family modules.

The family's elementary Pisot/irreducibility arithmetic and the published
tiling spectral implication remain outside these new Lean endpoints.
Termination here means finite reachability plus an available coincidence path;
the swap two-cycle still permits an infinite choice of noncoincident edges.
Arbitrary starting blocks, universal A1′, BH, C4, G1 and PSC are not proved
by this family-specific increment. All 126 governed claim statuses are retained.

## Replay

```sh
./tools/setup_lean.sh
./tools/check_c4_parameter_family.sh
./tools/check_lean.sh
python3 oracles/python/c4_parameter_family_carrier.py
python3 -m pytest -o addopts= -q tests/test_proof_bank.py
cd kernel
pixi run mojo run -I . tests/test_c4_parameter_family_carrier.mojo
```
