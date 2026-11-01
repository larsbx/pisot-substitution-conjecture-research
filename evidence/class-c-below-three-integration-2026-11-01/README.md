# PR #394 integration supplement, 2026-11-01

[Proof dependency and file audit](../../docs/class-c-below-three-integration-2026-11-01.md).

This supplement preserves both original packets byte for byte. `audit.json`
inventories all 142 original diff paths and their decisions, every original
packet file's SHA-256, the original #392 source revision and its three known
current drifts, and exact mainline theorem source identities.
`provenance-check.json` is the deterministic provenance-only guard output.
The two integration receipts check only the bounded assembly arithmetic
and actual packet inventory; they are not graph or PSC proofs.

Replay from the repository root:

```sh
python3 tools/check_class_c_below_three_integration.py
(cd kernel && pixi run --locked mojo run -I . tests/test_class_c_below_three_integration.mojo > /tmp/class-c-integration-native.log)
python3 oracles/python/check_class_c_below_three_integration.py /tmp/class-c-integration-native.log
python3 -m pytest -q tests/test_class_c_below_three_integration.py
```

The provenance guard requires full Git history. Original complete native and
independent graph replays remain those of the below-three packet; inherited
#392 evidence and replay sources remain historical, with its workflow bytes
in `archive/class-c-slope-three-2026-11-01/workflow.yml`. Native assembly is
canonical; the independent Python arithmetic oracle provides a finite
cross-check. Human review remains pending and no governed claim is promoted.
