# Shared checked indices and individual row decisions

This directory retains the intermediate monolithic candidate between
published commit `55ce68531aecb7a351e652dd5cf824ee8ac32a34` and the subsequent
data-module split. It was tested locally but not published as a separate
commit. **Its native results and diagnostic compilations are not complete
carrier or termination acceptance.**

## Representation and complete native replay

The emitter replaced repeated `⟨i, by decide⟩` row and seed occurrences
with transparent `noncomputable` constants carrying exactly those original
checked bounds. It emitted every index from zero through `n - 1` once.
It also partitioned the unchanged `Packet.checkRange` obligations into
single rows and combined them with the existing append and validity
theorems. No row occurrence, seed, predicate or complete endpoint changed.

`native-replay.tar.gz` contains the complete successful gate output,
including the two original JSON packets, both intermediate monolithic
Lean sources, source and binary manifests, commands, logs and receipts.
The gate passed in **65.908276 seconds**, with **230 tests passing in
61.04 seconds**. It reproduced both original packets and both candidate
sources byte for byte, retained both empty-output budget refusals, and
passed the independent oracle under Python optimization. Source bytes,
revision and executable hashes stayed unchanged.

The 44 additional controls reconstruct all ordered states, child
occurrences and six ordered seeds from the actual checked aliases. They
also verify the packet/accessor bindings and complete singleton coverage,
and reject corrupted bounds, values, declarations, rows, seeds and ranges.

| Identity | SHA-256 |
| --- | --- |
| Exporter binary | `be0233fa1850b9aa917df6e99368366ec75af4ed84c554e13bf5f4d4deec74a3` |
| Terminal native receipt | `bd929df1f145d4d57ae79080570ab2117118e18dffceec83b46606347a818230` |
| Native source manifest | `ec1dbad5103d7824beed754c34fabab4d0ed4578b5cc067f4bcc3f8bf1df95a1` |
| Intermediate fixture 0 Lean | `9194992968eca8ec61de9c8d3c0d1a0a78adabe166adc770240591b18c45b991` |
| Intermediate fixture 1 Lean | `7770595c93011209cad16d9e0f8acc670f9e24b8aa3dbc74429555f442d84d07` |

The gate truthfully records parent HEAD `55ce685` with modified candidate
files. Its binary was supplied; the separate source-bound build receipt
reproduced that binary digest from unchanged recorded inputs.

`intermediate-source-overrides.tar.gz` makes this unpublished candidate
reproducible: apply its four source overrides to commit `55ce685`. All
757 other source-manifest entries were verified against that commit, and
the four overrides were verified against their previously recorded gate
hashes. The emitter and test copies were restored by reversing later
source edits and required to match those exact hashes. Original execution
records were copied unchanged; no terminal result was reconstructed.

## Diagnostic outcomes

`proof-only-carrier1-controlled-stop.tar.gz` preserves the preceding
explicit-noncomputable source and full diagnostic records. Its fixed
4,000,000,000-byte RSS guard fired at a sampled peak of 4,087,095,296 bytes.
The runner sent SIGTERM and recorded `controlled_stop`, `rss_guard`,
return code `-15`, and **1,463.923243 seconds**. The source was unchanged
and no object was produced. This differs from the earlier unexplained
SIGKILL retained in the preceding follow-up packet.

`checked-index-probes.tar.gz` retains the exact Init-only row-array probes.
The original 4,386 repeated checked-index occurrences exceeded the
90-second bound without an object. Sharing the same 518 used checked
indices compiled in **5.458 seconds** and produced an object; expanding
the aliases reproduces the original row declaration byte for byte. These
observations motivated the representation change. They do not identify
the earlier full-process kill's cause or establish a controlled overall
speedup.

`monolithic-carrier1-requested-stop.tar.gz` retains the next exact
monolithic candidate run. It was deliberately stopped to implement the
tested data-module separation: `requested_stop`, return code `-15`,
**590.831 seconds**, sampled peak RSS **3,485,392,896 bytes**, unchanged
source and no object. This is an explicit cancellation, not a proof error.

`complete-data-init-probe.tar.gz` contains the complete 1,536-declaration
fixture-1 data prefix, with all included declarations preserved verbatim.
It compiled under Init in **39.513279 seconds**, with peak sampled
aggregate RSS **780,099,584 bytes**. The substitution, packet and carrier
proofs were excluded, so this result establishes only the data-stage
compilation used to motivate the subsequent split.

The two kernel-trace archives retain the reporting controls. Their object
hashes agree across logging wrappers and worker settings. The two-worker
control exposed completed names while still running; `Elab.async=false`
remained in effect. These are reporting controls, not carrier proofs or controlled
performance measurements.

The subsequent split and its independent replay are recorded in the
[split-data packet](../split-data-replay/README.md). All 126 governed claim
statuses remain unchanged throughout this work.
