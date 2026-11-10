# Two-tail uniform word proof: repository integration

**Status:** written parameter-uniform proof and locally replayed exact Python
controls; native Mojo port, Lean formalization, hosted acceptance and independent
human review remain separate outstanding work. No governed C4, A1', BH, G1,
BPA-termination, pure-discreteness or PSC claim status is changed.

This integrates the November 6 conversation bundle on
`main@ba09fdbd770248905a297303b8de45b3d7c5018d` at the owner's explicit request.
The complete proof is [the two-tail note](../experiments/c4_two_tail_uniform/docs/two-tail-uniform.md).
The original [source and instructions](../experiments/c4_two_tail_uniform/README.md),
[compressed-word verifier](../experiments/c4_two_tail_uniform/oracles/two_tail_uniform.py),
[tests](../experiments/c4_two_tail_uniform/tests/test_two_tail_uniform.py),
and [independent replay](../experiments/c4_two_tail_uniform/tools/independent_replay.py)
are preserved byte for byte.

## Scope

For all nonnegative integers a,b with a+b>=1, the two literal families
`(01,1^a 2 1^b,102)` and `(01,1^a 2 1^b,120)` have pairwise source-letter
strong coincidence by generation five. When a>=1 the proof exhibits a
simultaneous three-letter witness at generation four. The a=0 boundaries
have separately proved identities, including the b=1,2 exceptions for tail
102. Five is sharp as a common source-pair bound, not necessarily the least
productivity time of each balanced root.

Consequently every nonempty balanced root has an actual diagonal in its
complete fifth inflation. This is independent of its length or a proposed
finite component, and applies to unbounded determinants a+b. It does not
establish finiteness of all descendants, arbitrary-source C4, pure discrete
spectrum, or PSC. The full note includes all hypotheses, block-word
inclusions, boundary exceptions, the sharpness control and a conditional
finite residual-matrix contraction bound.

## Reproduce without modifying historical evidence

From the repository root:

```sh
python -m pip install 'pytest==9.0.2' 'sympy==1.14.0'
python tools/check_c4_two_tail_uniform_bundle.py --output /tmp/psc-two-tail-replay
python tools/make_proof_bank.py --check
```

The wrapper restores the two identical large receipt files from the
losslessly compressed `receipt.json.gz` in a temporary copy. It then checks
all 18 original file pins against the archived SHA-256, Git blob SHA and
byte count before running tests, the independent replay and receipt
regeneration. The original proof, code, tests, failed symbolic-harness
attempt and later successful logs are unchanged. The historical manifest
is not relabelled as this integration's execution. Fresh logs go only to
the separately requested output directory. `--verify-only` reports only
hash authentication and never claims test execution.

Fresh local integration replay passed all 19 tests, 288 independently
reconstructed source prefixes (168 checked by materialized words), eight
symbolic identities and receipt equality. The finite grid covers 880
source/parameter choices; the unbounded argument remains the written proof.
The workflow requires the exact PR head and repeats the fresh replay.
Full-repository Proof Bank/governance and hosted results are not claimed
as locally executed. Existing generated inventories and formal sources are
not manually rewritten.

## Python-only integration exception and native work remaining

This is an explicitly scoped proof-and-secondary-prototype import, not a
new canonical execution path. The verifier supports 512-bit run parameters
through exact compressed word DAGs. A correct native port must bind that
DAG's prefix/character operations to the repository's checked BigZ layer
and receive exact native/oracle parity. Mojo/pixi are unavailable in the
integration runtime, so that port cannot be compiled or validated here;
a machine-Int transcription would not preserve the advertised domain.
The written proof and exact Python evidence are therefore integrated with
this documented blocker, without fabricating a native implementation or
using the unrelated #500 Lean results as evidence. Existing Mojo-first
kernels, APIs and their authority are unchanged.

Related research tracking: issue #461. The merge is authorized repository
integration, not independent mathematical endorsement or a hosted CI pass.
