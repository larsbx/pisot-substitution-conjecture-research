# Fixture-1 consumer conversion depth probe

These are focused cached-dependency probes of the consumer conversion that failed in the hosted archive and full Lean builds. They import the actual successful `PscVerif.NamedForwardCarrierData1` object. They do not compile the full `NamedForwardCarrier` module and do not establish fixture-0, termination, or complete isolated acceptance.

The literal substitution table matches the named table. The selected fixture-1 carrier is unchanged. The unused fixture-0 carrier entry is an empty list solely to avoid importing the missing local Data0 object; no assertion about that entry is made. The closed statement in all three variants is `check 1 (checkedStates 1) = true`.

## Observed results

| Variant | Exit | Result | Elapsed seconds | Maximum sampled RSS bytes |
| --- | ---: | --- | ---: | ---: |
| Baseline | 1 | failed | 34.361255 | 2659405824 |
| LocalDepth | 0 | passed | 14.235286 | 2669539328 |
| Selectors | 0 | passed | 12.622644 | 2668728320 |

- `Baseline.lean` keeps the original `change` tactic and default recursion depth. It reproduces `maximum recursion depth has been reached` at line 19, column 2. No object is produced. The audit then refuses the `sorryAx` introduced by Lean error recovery; that refusal is additional protection against mislabelling the error as proof acceptance.
- `LocalDepth.lean` differs only by the theorem-local `set_option maxRecDepth 200000 in`; it compiles and passes the axiom audit.
- `Selectors.lean` retains the default recursion depth and instead simplifies only `check`, `checkedStates`, `substitution`, `Matrix.cons_val_one`, and `Matrix.cons_val_zero`, then applies the existing generated `fixture1ForwardCheck`. It neither unfolds `Psc.ForwardCarrier.check` nor decides the concrete carrier again. It compiles and passes the axiom audit.

Each successful audit checks the transported theorem and the actual generated ForwardCheck theorem, allowing only `propext`, `Classical.choice`, and `Quot.sound`. All three runs retained unchanged input bytes. Neither the 600-second wall guard nor the 4,000,000,000-byte RSS guard fired; RSS sampling interval is 0.25 seconds. The variants ran sequentially, with changing cache state, so the elapsed times are not a controlled performance comparison.

## Binding and replay

`run.py` records the compiler identity, command, environment, complete local import-closure source and object hashes, and direct external cached dependency boundary hashes. The transitive external dependency objects are explicitly identified as a remaining cached trust input. Each run uses a fresh output directory and refuses to overwrite it. The successful Data1 source/object and successful original terminal receipt are checked before starting.

Run from `/workspace/scratch/91efcf4b7b58` with `python carrier-diagnostics/consumer-depth-probe/run.py Baseline`, then `LocalDepth`, then `Selectors`; retain the existing evidence first, as the runner refuses existing variant directories. The source and compiler paths are explicit in the runner and receipts.

## Terminal receipt hashes

| Variant | receipt.json SHA-256 |
| --- | --- |
| Baseline | `257334dcd8ec3e753503ba50d17ce3e0002cc844d96d437c1577eede64f6630a` |
| LocalDepth | `fe34e58e871ab313d275e5fbdf6acd2db3335da21675901cdbc6d6d40de461b7` |
| Selectors | `af8f471807c51a6d0fb02104a19cd6fa5219dfa20a044d3c49698cacc5779dcf` |

Each variant directory contains `start.json`, `receipt.json`, the complete compiler log, resource samples, input manifest, and file hashes. Successful directories also contain their generated objects. The top-level `SHA256SUMS` covers the full retained packet.
