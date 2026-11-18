# Neutral-rank obstruction — local evidence, 17 November 2026

This packet supports the [mathematical review](../../docs/c4-neutral-rank-obstruction-2026-11-17.md)
and [literature decision](../../docs/c4-neutral-rank-literature-2026-11-17.md).
It records a conditional source-orbit bound, counterexamples to intermediate
inequalities, and a rank-one calibration. It supplies no strict PIP3 component
and no universal C4 or PSC proof. The changes are prepared locally for owner
review; there is no new pull request, publication, merge to remote main, or
hosted acceptance result.

## Revisions

| Input | Exact revision |
| --- | --- |
| #601 seam formula, branch head | `f5e2aab7d434f24dcbe618d4948984daa1e1a123` |
| #601 merge | `2d831230c9b5a2f7b21165df6756532b3f598e37` |
| #602 bounded literal constructor, still draft on inspection | `cbb8c6c64b56bcce60c2e6031da7acb9ffc5b41d` |
| #603 alphabet correction, branch head | `8d546126ebc33feac2ba9712345e087ee6cadfe1` |
| #603 merge / fetched main | `9dffd8ad19085c61e211eee85645e7f5e1ab8d09` |
| Local integration of #602 and fetched main, before this increment | `1cf7a6ccac6b20957e153cd8e7f6fd09bb594368` |

The [manifest](manifest.json) binds the final mathematical executable source
bytes and the runtime lock. A source digest, rather than a self-referential
commit field, binds the tests to the containing review commit.

## Tests actually executed

| Local check | Result and scope |
| --- | --- |
| [New seam-budget regression](neutral-seam-budget.log) | Exit 0; final contract receipt. Seven full source boxes have zero aligned nonproductive sinks. Three new source/power comparisons check complete endpoint, ordered seam and interior identities at powers 4, 2 and 3, with literal source occurrence replay. 1,476 exact invariant-subgraph/sign checks establish the finite controls for the bound and its sharpness. Includes the omitted-negative-orbit control, a four-letter endpoint-cycle control, invalid target/period refusals, and replay of the existing four-state `10/102/211` strict closure followed by refusal of its disconnected source graph. |
| [New rank-one calibration](neutral-rank-one-control.log) | Exit 0; final contract receipt. Exact positive unit PIP incidence, literal `T13`, rank-one swap span, neutral tensor transport, safe machine-integer bounds and an actual first coincident child in the explicit run-length realization. |
| [Source neutral-sign probe](source-neutral-probe.log) | Exit 0; complete footer. Traversed all 4,554 canonical corpus specimens, computing certified complete interior cycles for the 492 unit sources with source Betti number at least two, using 144 cached incidence matrices. No cap or arithmetic refusal. Found 12 positive full source-product corrections at +1, 12 positive corrections at -1 with determinant -1, and 12 sources where omitting a negative orbit raises the +1 budget. This is a source-graph probe, not a new strict-component census. |
| [Provenance profile](provenance.log) | Exit 0. Source provenance, vendoring, generated inventories, Markdown source integrity and claim governance passed. |
| Markdown links | All four checks in `tests/test_markdown_links.py` passed when executed directly as Python functions, including all tracked relative links. No pytest run is claimed. |

The original 48 comparisons from #602 were not rerun or counted as a new
result. The three new comparisons are targeted at the new counterexamples.
No full Mojo suite, new Lean build, isolated Lean axiom audit, Quint/TLA+ run,
or hosted CI run is claimed. The existing Lean declaration
`StrictSystem.deg23_iii` was inspected at the input revision; its proof was
not recompiled in this session. Independent mathematical/code audits found
no blocker; this is not independent human approval.

## Reproduction

From the repository root, in the locked runtime:

```sh
cd kernel
pixi run --locked mojo run -I . -I tests tests/test_neutral_seam_budget.mojo
pixi run --locked mojo run -I . -I tests tests/test_neutral_rank_one_control.mojo
pixi run --locked mojo run -I . neutral_seam_probe.mojo
cd ..
bash tools/verify_all.sh provenance
```

The local executable was the cached `Mojo 1.1.0.dev2026090805 (34562fa1)`
matching the existing lock, invoked with its `MODULAR_HOME`. The manifest
records the actual commands, source hashes and installed compiler hash. The
runtime's harmless Crashpad warning is preserved in the logs.

The complete periodic-state search uses the inherited 2,000,000-state cap;
the full overlap boxes use 400,000 states; seam adjacency saturation uses
100,000 types. The literal constructor permits at most 100,000 letters in
each expanded image and 100,000 records per population, and retains the
original-image length-six screening gate. Caps and rejected exact arithmetic
raise before any conclusion. The large rank-one matrix is a separate fixed
tensor control with its own verified integer bounds, not an input to that
bounded overlap or literal-seam constructor.

## Interpretation

`01/122/201` gives full-box correction `(1,1)` with determinant +1;
`12/012/221` gives `(0,2)` with determinant -1. They refute nonpositivity at
the determinant-selected neutral sign from source geometry plus the source
cohomology threshold. Both are productive controls, not counterexamples to a
theorem requiring an actual strict component.

`12/120/221` has period-three and fixed interior orbits contributing +1 and
-1 at +1. The full source correction is zero, while the invariant subgraph
over the period-three orbit has correction +1. This shows why the source-only
upper bound uses positive parts. That subgraph is not claimed to be a literal
child-closed strict carrier.

The bound is sharp for each sign separately among invariant subgraphs of the
source product. The two sign maxima need not be achieved by the same subgraph.
Its application to a strict bigon matrix retains all the realization, rank-two,
complete occurrence and trace-transfer hypotheses listed in the mathematical
note. No governed claim status changes.
