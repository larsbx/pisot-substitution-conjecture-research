# Class-D word-counter source rebind

The original Class-D assembly and integration packets retain their source
hashes and native receipts. This packet binds the three edited word sources
to the successful [complete plus-chamber replay](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43171890662/job/131026925051)
on PSC PR #551 at head `294ae330de2938c4eea2cc7c6234639fb8780437`.
The checkout used merge commit `51518eb507a4b730e09092637f23986d541838ea`.
It printed the same complete native receipt line as the October 30 rebind.
The three source files retain identical bytes in the reconciled PR.

Replay the provenance checks from the repository root with full Git history.

```sh
python tools/check_class_d_closure_rebind.py
python tools/check_class_d_assembly_evidence.py
python tools/check_class_d_integration_ci.py
```

The packet supplies source provenance for the three named paths. Its authority
is the existing rebind contract and the scoped finite native replay.
