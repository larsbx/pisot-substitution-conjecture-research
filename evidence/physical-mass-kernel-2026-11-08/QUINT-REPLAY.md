# Local Quint physical-mass replay

The accepted model source is `proof/quint/PhysicalMass.qnt`. Run from the
repository root:

```bash
python3 tools/check_physical_mass_quint.py --output /tmp/physical-mass-quint
```

The runner requires Quint **0.33.1**, invokes the TypeScript backend explicitly,
and refuses missing tests, a changed test inventory, a mismatched version,
typecheck errors, timeouts, or a mutated model that escapes its expected failing
assertion. Typecheck and every baseline suite consume one private read-only
snapshot of the captured model bytes; all mutants derive from that snapshot.
Before acceptance the snapshot, live model, runner bytes and Git HEAD must
still match their captured identities. An earlier receipt is reset before
source reads, so initialization errors cannot leave a stale successful status.
Each of the 20 named tests executes once. There is no nondeterministic
choice in these tests; the seed is pinned for reproducibility and does not make
sampling exhaustive.

## Finite domains

| Check | Exact quantified domain |
| --- | --- |
| Matrix pairing, saturation, loss and zero propagation, source-SCC nullity | All 11,664 tuples: 81 matrices in `{0,1,2}^(2×2)`, four masses in `{1,2}²`, nine vectors in `{0,1,2}²`, four scales in `{0,1,2,3}` |
| Reachability and source ancestors | All 512 directed graphs on three vertices, including loops; closure is compared to an independent path-of-length-at-most-two expression |
| Source-SCC loss versus reachability from loss | All 4,096 graph/loss-set pairs |
| No premature stable zero set under source loss | All 32,768 graph/loss-set/known-set triples, with the stated implication antecedents |

These are domain cardinalities, not random runs or a claim that every internal
conditional branch executes. The matrix implication checks its conclusion only
when its explicit numerical premises hold. Separate accepted and conservative
fixtures guard against empty useful domains.

The transition module starts with the single losing vertex of the source SCC
of

```text
T = [[0,2,0], [1,0,2], [0,0,0]], h = [1,1,1], theta = 2.
```

Its transpose deficit is `[1,0,0]`. The deterministic trace grows the certified
zero set from `{0}` to `{0,1}` and then `{0,1,2}`. Reverse, absent and already
covered edges cannot supply a new propagation step.

## Adversaries and mutation gate

The eight adversarial tests cover a conservative source, a losing sink mistaken
for a source, a deleted repeated occurrence, row mass substituted for transpose
mass, zero mass hiding nonzero slack, incomplete root reachability, a negative
matrix entry hiding cancellation, and a signed overlap vector.

Six source mutations must reach and fail their named test assertions. The
receipt records the exact single replacement, mutant SHA-256 and failure-log
SHA-256. Parse errors and a zero test selection never count as a successful
negative control.

The zero-mass fixture concerns the saturation step: nonnegative mass with a
zero coordinate can hide nonzero slack even when the weighted conservation
identity holds. It also lacks source-loss coverage. No example is claimed to
retain every other full nullity premise while defeating the theorem.

The omission fixture explicitly distinguishes the actual and supplied matrices.
Deleting a repeated occurrence manufactures loss, but the supplied matrix does
not satisfy the original nonzero overlap vector's inequality. Source identity
must prevent these two different matrices from being spliced together.

## Receipt scope and backend comparison

`quint-local/quint-receipt.json` records 20 successful tests and six rejected
mutations, `source_snapshot_used: true`, and the successful source/revision
recheck. It binds the actual model and runner bytes by SHA-256. Its Git HEAD
is the pre-existing base at the time of local work and `worktree_dirty` is true:
this local receipt does **not** accept that base as a revision containing these
new files. Hosted execution must supply its own exact-revision receipt.

All 20 tests also pass under Quint's Rust backend, runtime **0.7.1**. The four
additional logs and `quint-local/backend-comparison.json` bind that comparison
to the same model bytes and record the local native executable digest. The
comparison command is recorded in that JSON; it uses the same module names,
seed and single-test count with `--backend=rust`.

## Retained unsuccessful helper formulation

`quint-helper-reproducer.qnt` is a historical negative diagnostic, separate from
the accepted model. For `T=diag(2,0)`, `h=[1,1]`, `theta=2`, its nested generic
list-map helper produced `[0,0]` instead of the mathematical deficit `[0,2]` in
both local backends. The TypeScript trace shows the incorrect second entry;
both logs retain the failing expected-value assertion. Reproduce with:

```bash
npx --yes @informalsystems/quint@0.33.1 test \
  evidence/physical-mass-kernel-2026-11-08/quint-helper-reproducer.qnt \
  --main=PhysicalMassHelperReproducer --max-samples=1 --seed=20261108 \
  --backend=typescript --verbosity=3
```

Exit status 1 from that named mathematical assertion is the recorded
observation; it is not an accepted proof failure. Replacing `typescript` with
`rust` reproduces the other log. The accepted model uses direct folds, pins
the expected diagonal and asymmetric products, and passes the entire finite
suite in both backends. This packet records observed formulation behavior
without assigning an upstream defect diagnosis.

No Quint result here establishes a universal real-matrix theorem, authenticates
PR #515's literal graph, proves a geometric overlap measure premise, or closes
general C4 or PSC. Those are separate deductive, refinement and mathematical
obligations.
