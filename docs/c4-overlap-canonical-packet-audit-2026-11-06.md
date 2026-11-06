# Canonical overlap packet: concrete acceptance and mutation controls

## Assumptions and hypotheses

This follow-up inspects PR #500 at exact revision
`40e5ecf3291ecba68c687fb94f1007d0f176ca89`. The supplied `73aea7d7` baseline
has been superseded: the later branch already implements the requested
canonical Mojo-to-Lean importer, typed conversion, kernel checking and full
independent packet comparison. This work reuses it and adds genuine-packet
mutation coverage and reproducible artifact inspection. No Lean theorem,
claim status, dependency edge or mathematical implementation is changed.

Source 0 is `0 -> 1, 1 -> 012, 2 -> 001`. Its canonical packet has 15,824
ordered states, 78,333 occurrence edges, 334 weight sweeps, positive integer
weights at most 61,428, and minimum integer row slack 102. Root weights are
51,342 / 8,165 / 27,199. These are exact finite data, not numerical estimates.

## Derivation / reduction

The producer is `kernel/c4_overlap_lean_export.mojo`. It serializes the
canonical native graph into a balanced lookup tree of packed unbounded
natural literals. Layout proofs bind tree lookup to ordered leaves; rows keep
each occurrence in its original order, including parallel targets. Decoding
checks bounds and positive weights before constructing `Fin` targets.
Kernel proofs cover every consecutive row range and compose into
`packet.check = true`, followed by the existing typed `Certificate.check`.
The independent auditor checks the exact proof types, audits all generated
declarations and emits the same `packet` directly. Python independently
reconstructs every state, row occurrence and weight and compares the full
serialization, including rejection counters and sweep metadata.

Every row satisfies

$$20\sum_{e\in\mathrm{row}(i)}w_{\mathrm{target}(e)}\le102w_i.$$

The exact Python root-isolation replay checks `beta^2 > 103/20`, so the
comparison rate `102/20` is strictly smaller, with a margin greater than
`1/20`. This is not a new Lean proof identifying the actual Perron root:
`Certificate.class_rate_null` retains that spectral premise and the complete
geometric recurrence as explicit inputs. Packet acceptance alone does not
instantiate them.

The newly extracted `verify_source_stream` is the same exact line comparison
previously in `verify_native_file`; both the complete-class verifier and the
new mutation regressions use that routine. The class verifier still requires
the schema, all sources 0..17 in order and EOF. No canonical graph or weight
algorithm changes.

## Evidence and replay

The exact-head [packet run 42171568610](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/42171568610)
and separate [generic Lean run 42171568712](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/42171568712)
completed successfully at `40e5ecf3`. This supersedes the integrated-head
pending observation in the earlier integration note only at this exact scope.
The downloaded packet artifact is
[13484799116](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/42171568610/artifacts/13484799116),
180,953,671 bytes, SHA-256
`abc9b4f5b45dcb0bc24b362afacf6f38295a504e90939f8abd467f00f8e710e9`.
The downloaded ZIP matches GitHub's recorded digest.

Inspection checks the revision file, all 18 generated source/log hashes,
all independent auditor sources, complete declaration/axiom records, empty
stderr files, reconstruction of the packet from audit logs byte for byte,
and the stored oracle receipt against the committed canonical receipt.
An additional fresh full Python reconstruction repeats the complete packet
comparison. This is fresh runtime data-parity evidence using retained hosted
kernel evidence; **no fresh local Lean compilation is claimed**.

| Evidence at `40e5ecf3` | Result |
| --- | --- |
| Typed kernel packet checks | All 18 sources / 285,786 states / 1,409,729 occurrences |
| Generated declaration audit | 2,564 declarations / 1,539 theorem declarations per source |
| Generic audit | 531 declarations / 275 theorem declarations / 106 named proofs |
| Allowed axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Full packet SHA-256 | `87403bd9b3e9d88093f6b90969e3b04d1a8855893a55ec3fb28725892c43591e` |
| Real wrong-proof-type fixture | Compiles, then independent expected-type audit refuses |

Costs below are from the hosted receipt, not predictions for another host.
Per-source time combines Mojo generation, Lean compilation and the independent
type/axiom/emission audit; it does not separate those phases. Peak RSS was not
recorded. Dependency provisioning, generic build and final Python parity are
outside those per-source totals.

| Measurement | Observed |
| --- | ---: |
| Source 0 combined time | 242.202 seconds |
| Per-source combined range | 233.006–284.966 seconds |
| Sum across 18 sources | 4,633.095 seconds (77.218 minutes) |
| Source 0 generated Lean | 1,551,711 bytes |
| Source 0 compiled module | 40,678,736 bytes |
| Generic `OverlapPacket` module build in hosted log | 4.0 seconds |

The archived earlier source-0 and period-three source-12 pilots precede the
all-18 run; this session did not launch a new all-18 kernel build. Reproduce
the canonical importer/kernel path as documented in
[the packet binding note](c4-overlap-lean-packet-binding-2026-11-05.md).
For a bounded source-0 replay after provisioning/compiling the pinned Lean
project and canonical Mojo exporter:

```sh
python tools/replay_overlap_lean_packets.py \
  --exporter /tmp/c4-overlap-lean-export \
  --project /absolute/path/to/compiled-pinned-PscVerif \
  --root "$PWD" --output /tmp/fresh-source0-replay --source 0
```

Such a development receipt deliberately says `all_18_sources_verified: false`.
The isolated all-18 gate remains `tools/check_lean.sh --overlap-packets`.
The pinned Lean/Mathlib versions and codec/resource caps are unchanged.

After downloading and extracting the exact hosted artifact, independently
inspect its binding and rerun Python reconstruction:

```sh
python tools/audit_overlap_lean_artifact.py \
  --artifact /absolute/path/to/extracted-artifact \
  --revision 40e5ecf3291ecba68c687fb94f1007d0f176ca89 --reconstruct
python -m unittest discover -s tests -p test_overlap_lean_packet_replay.py -v
```

The inspection tool refuses a different revision. It does not authenticate
arbitrary artifacts or replace trusted hosted/source/compiler provenance.
Small receipts, full generic log, source-0 Lean source and complete audit/packet
log are retained in
`evidence/c4-overlap-canonical-packet-audit-2026-11-06/`; compressed payloads
have uncompressed SHA-256 entries in `payload-manifest.json`. Full all-source
payloads are in the linked hosted artifact with its 30-day retention policy;
they can be regenerated with the pinned source. This follow-up revision has
local regression evidence, not a newly relabelled all-18 kernel receipt.
The 22 existing complete-class oracle regressions and proof-bank consistency
check also pass. Fresh full Python reconstruction took 66.117 seconds locally.
The inspected hosted job explicitly passed the canonical Mojo exporter tests
and build before its isolated Lean replay.

## Negative controls

Eleven local tests pass: five existing audit-protocol tests and six new
source-0 serialization tests. The positive source-0 packet matches its
committed SHA-256
`721f0bcbca2f91d1a7e1613751f446defa7ad85b0316bfe391faeb401d85ccef`.
The new controls exercise the production source-stream verifier and refuse:

- An omitted occurrence, a duplicated occurrence and collapsed parallel edges.
- A changed in-range target chosen to have the same weight, preserving the
  row sum exactly.
- Zero and corrupted positive weights.
- Reordered state labels, a missing row, truncation and a header-only packet.
- A complete source-0 packet presented as an incomplete 18-source class.

Omission and collapse explicitly retain the row inequality. Their refusal is
due to canonical occurrence comparison, not a stronger claim about what the
integer checker alone can detect. These new regressions are runtime tests,
not kernel proofs of geometric completeness. Existing kernel controls for
invalid indices, multiplicity, zero weights, missing rows, wrong tree cuts
and hidden payload remain intact.

## Non-claims / remaining gaps

Concrete packet binding is accepted at the recorded hosted revision. Four
geometric and measure-theoretic bindings remain:

1. Prove refinement from every actual paired-prefix occurrence to its recorded
   graph target, including sound empty-piece pruning and absence of omitted
   geometric cover terms.
2. Construct the matrix-adic completion and Haar measure, prove the index-two
   image and actual product-measure scaling.
3. Construct the actual compact-prefix operator and prove its contracting
   iterate and fixed-set identities, including the period-three cases.
4. Prove fixed-origin strict-cut counting and the positive lower measure bound
   in the same normalization.

Compiler/producer fidelity and the bridge from arithmetic data to actual
geometry remain explicit trust/refinement inputs. This neither proves the
full concrete geometric overlap theorem in Lean nor promotes general C4,
G1, PDS or PSC. No mathematical changes or PR are merged.
