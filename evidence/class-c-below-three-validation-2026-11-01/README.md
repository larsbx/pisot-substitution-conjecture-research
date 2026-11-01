# Class-C below-three fresh local validation, 2026-11-01

This is a new supplement; neither original packet nor the first integration
supplement is edited. [Dependency reconciliation](../../docs/class-c-below-three-integration-2026-11-01.md).

`import-closure.json` binds the 57 local Mojo import sources and records the
real external roots `std` / `max`. Docstring/comment pseudo-imports explain
the original metadata's extra roots `a`, `it`, `the`; they are not missing
source dependencies. The original source hashes are preserved.

An isolated import probe of the independent Python entry point additionally
finds package initialization through `reference/psc_research/__init__.py`
and `reference/psc_research/bpa.py`. Those two executed sources were not in
the original manifest. Their exact hashes are recorded here as supplemental
provenance, not retrospectively inserted into the old packet. The explicit
oracle modules still match their original hashes. Python, its standard
library and the Mojo compiler/runtime remain trust inputs.

Replay:

```sh
python3 tools/check_class_c_below_three_imports.py
python3 -m pytest -q tests/test_class_c_below_three_imports.py
```

The tested development environment needs SymPy 1.14.0 for three already
present Class-A symbolic test modules. `pyproject.toml` now declares that
missing test dependency; this repairs clean-environment collection and
changes no mathematical kernel. Native plan and independent graph replay
receipts, when recorded alongside this file, are local validation only.
No hosted or independent human-review result follows from this supplement.

The test-dependency edit initially caused the Class-D historical source
provenance guard to refuse. `failed-dev-dependency-provenance.log.base64` (base64 encoding of the unedited raw log) preserves
that refusal. Its repair is an explicit, exact additive-dev-dependency
exception with negative controls; historical Git bytes/hashes are still
verified, and no previous receipt is changed. Fresh final-head hosted
acceptance remains a requirement. See the integration note for its precise
limits and the 43 passing Class-D integration/rebind regressions.
