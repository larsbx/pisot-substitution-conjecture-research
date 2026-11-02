# Conditional finite quotient-distance Lean acceptance

Implementation source: `85343b90a06a3c119198370900fca493032c47e9`.
The source tree and every local proof module, checker, dependency pin and
adapter source are pinned alongside the receipt. Later evidence-only commits
do not change the checked proof implementation.

This packet concerns sixteen new named Lean proofs in
`PscVerif.QuotientDistance`, imported by the root proof bank. It proves a
conditional finite graph statement: explicit edge projection, lifting from
every actual source and typed terminal equivalence preserve all terminal path
lengths, absence of terminal paths and shortest lengths. A selected witness
plus every-edge rank inequalities certifies exact shortest distances.
It does not prove native acceptance supplies those semantic premises.

`core-build.log` is the fresh direct compilation output at the implementation
revision. `core-axioms.log` queries every new named proof; the exact query text
is preserved. `focused-tests.log` records the 193-test proof-bank, evidence,
source-manifest and link suite. `provenance.log` records governance/provenance
checks. `source-check.log` verifies the source manifest at this revision.

The full isolated `tools/check_lean.sh` replay **passed**: 303 compiled
declarations, 174 compiled theorems and **all 68 named proofs reached**.
The new module contributes 51 compiled declarations / 23 compiled theorems,
including all sixteen named proofs; its axiom union is only `propext` and
`Quot.sound`. No local/nonstandard axiom is accepted. `isolated-audit.log.gz`
preserves the full run, including dependency checkout/cache checks, fresh
project compilation and final axiom report. The unchanged script copies only
source/configuration to a fresh workspace and refuses dependency source drift.

`receipt.json` records outcomes and exact scope. All files in this packet are
pinned by `SHA256SUMS`. This is local source-revision acceptance with the
explicit environment qualification below; new hosted Lean acceptance is
pending. The earlier #447 hosted finite execution result is a separate packet.

## Environment qualification

Pinned Lean 4.34.0-rc2, compiler commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`. The normal unadapted executable
fails before elaboration in this environment; `unadapted-startup.log` retains
that failure. The existing path-only compatibility adapter in
`evidence/research-integration-postmerge-2026-11-01/proc_self_compat.c` was
compiled and used only through per-command LD_PRELOAD. Its negative controls
are recorded, and `adapter.json` pins its source location and binary digest.
No theorem, compiler, checker or dependency source is patched. This is a
qualified local execution, not an unadapted hosted pass or human review.

Normal hosted replay uses the existing project scripts **without the adapter**:

```sh
bash tools/setup_lean.sh
bash tools/check_lean.sh
python -m pytest -q tests/test_proof_bank.py tests/test_recorded_data_integrity.py tests/test_research_source_manifest.py tests/test_markdown_links.py
```

For local compatibility replay, compile the already archived adapter source
with `cc -shared -fPIC -Wall -Wextra -Werror SOURCE -ldl -o /tmp/libpsc_proc_self_compat.so`,
then use `LD_PRELOAD=/tmp/libpsc_proc_self_compat.so` with the unchanged pinned
commands. The negative-control source is named in `adapter.json`. This runtime
qualification is an additional trust input and must accompany local results.

## Scope boundary

No verified Mojo decoder, fixed-width arithmetic/occurrence-to-Lean refinement,
parameter-uniform X carrier, nonunit realization bridge, BH or general PSC
promotion. Claim status and Lean/Lake pins are unchanged. The standard graph
lemma carries no novelty claim; independent human review remains pending.

[Contract and premise matrix](../../docs/finite-quotient-distance-lean-2026-11-02.md)
· [pre-implementation gate](../../docs/finite-quotient-lean-stopgo-2026-11-02.md)
· [separate hosted finite acceptance](../class-a-finite-hosted-acceptance-2026-11-02/README.md).
