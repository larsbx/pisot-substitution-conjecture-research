# Research integration local replay, 2026-11-01

Candidate against main 3967ab32384e4add7c6d42a7519f42932c8625cb.
The original PR heads and all evidence blobs are recorded separately.
These local results do not imply hosted acceptance or independent human
proof certification. No general PSC conclusion is asserted.

- 31 distinct native test files pass after the row-12 API correction. The
  initial compiler failure is retained; the final native log supersedes it.
- 240 symbolic selected paths, 1,326 oriented edge checks and 800 native
  member paths; original universal absence arguments remain separately scoped.
- 32 complete four-/nine-seed graphs: exact five-tuple vertex equality and
  every occurrence-edge multiplicity agree with an independent Fraction oracle.
- 186 Class-B rays: native counts exactly equal independent polynomial
  expansion counts; the unchanged offline wrapper is used on every native ray.
- 47 selected Python tests and 16 targeted tests pass (overlapping suites;
  counts are not added as though distinct). Further broad checks are recorded
  separately when complete.
- Fresh Lean audit is incomplete: pinned executable startup fails.

Replay from repository root with the locked Pixi compiler:

```sh
pixi run --locked --manifest-path kernel/pixi.toml bash -c 'cd kernel && mojo run -I . tests/test_class_a_selected_exit_integration.mojo'
pixi run --locked --manifest-path kernel/pixi.toml bash -c 'cd kernel && mojo run -I . tests/test_class_a_finite_hub_integration.mojo && mojo build -I . class_a_finite_hub_integration.mojo -o /tmp/finite-hub'
python oracles/python/check_class_a_finite_hub_integration.py /tmp/finite-hub
python -m pytest tests/test_research_source_manifest.py tests/test_recorded_data_integrity.py tests/test_class_d_plus_row12_symbolic.py
python tools/check_class_c_below_three_integration.py
bash tools/check_lean.sh
```

See ../../docs/research-branch-integration-2026-11-01.md for quantifiers,
source exceptions, negative controls and the complete PR disposition.
The source bindings identify these local runs; the hosted workflow records
its actual tested Git head separately. Original packets are never refreshed.
