# A finite source-SCC physical-mass verification kernel

This work formalizes the conditional matrix argument in
[PR #515](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/515),
at source revision `51dd090a6aefeb92210410a3f7e20d51926d7e86`.
It targets main independently of the unmerged #497/#515 implementation stack.
The [literature decision](physical-mass-kernel-literature-gate-2026-11-08.md)
records the standard nonnegative-matrix background and the geometric limits.

The module [PhysicalMass.lean](../proof/PscVerif/PscVerif/PhysicalMass.lean)
contains 26 named theorem statements. The local compiled audit covers all
65 declarations, including 40 theorem declarations after generated helpers,
and admits only the three standard axioms used by the existing proof bank.
Its source-scoped local receipt is retained in
[lean-local](../evidence/physical-mass-kernel-2026-11-08/lean-local/README.md);
isolated exact-head hosted verification remains a separate receipt.

## Assumptions and mathematical contract

Let `I` be any finite index type, `T : I × I → ℝ` a nonnegative matrix,
`h : I → ℝ` strictly positive, `v : I → ℝ` nonnegative, and `θ : ℝ`.
All vector inequalities below are coordinatewise. Assume

\[
Tv\geq\theta v,\qquad T^{\mathsf T}h\leq\theta h.
\]

No independent assumption `θ > 0` is needed by the implication. In the
physical application `θ = β² > 0`. Empty index types give the empty zero
vector without a source-component existence claim.

The graph convention is part of the contract: `i → j` means `T[i,j] > 0`.
Rows are inverse parents and columns are inverse children in #515. Define

\[
r_i=(Tv)_i-\theta v_i,\qquad
e_j=\theta h_j-\sum_i T_{ij}h_i.
\]

Thus `e = θh − Tᵀh`, not `θh − Th`. A losing vertex has `e_j > 0`.
A source SCC has no incoming edge from a different SCC in this orientation.

## Derivation

Finite distributivity and interchange of the two finite sums give the
exact deficit identity

\[
\sum_i h_i r_i+\sum_j e_jv_j=0.
\]

Both sums are nonnegative. Every summand is zero. Strict positivity of
`h_i` forces `r_i = 0`, so the assumed supersolution saturates:
`Tv = θv`. A positive deficit similarly forces its coordinate `v_j = 0`.

If `v_i = 0`, its saturated row is

\[
0=\sum_j T_{ij}v_j.
\]

Every term is nonnegative, so a positive `T_ij` forces `v_j = 0`.
Induction on a finite directed path propagates this zero along inverse
edges. A losing vertex therefore zeros every vertex reachable from it.

The finite graph lemma provides a source-SCC ancestor for every vertex.
Inside an SCC each vertex reaches every other vertex. Consequently,
one losing vertex in each source SCC reaches the entire finite graph,
and every coordinate of `v` is zero. SCCs and matrix size are arbitrary;
there is no bounded enumeration in this implication.

For a selected target set, the direct sufficient condition is that each
target be reachable from a losing vertex. Root coverage is a separate
source-refinement obligation: the abstract theorem says nothing about
coordinates omitted from the supplied index type.

The checked interfaces are in namespace `PscVerif.PhysicalMass`:

| Interface | Scope |
|---|---|
| `zero_of_source_loss` | The general finite real-matrix obstruction |
| `sourceLoss_iff_loss_reaches_all` | Source-SCC loss exactly characterizes graph coverage from losing vertices |
| `zero_on_targets`, `zero_of_root_cover` | Selected-coordinate and explicitly complete-root variants |
| `conservative_source_ancestor_of_nonzero` | A surviving coordinate has a source-SCC ancestor on which every deficit is zero |
| `weighted_transpose`, `weighted_deficit`, `weighted_loss_iff` | Correct physical transport for mixed track-swap orbit sizes |
| `Refinement.of_forward_mass` | Constructs a proof-valued certificate interface from supplied forward budgets and transport proofs |
| `Refinement.zero_of_supersolution` | Applies that interface only after receiving the nonnegative overlap vector and its actual supersolution proof |

## Evidence layers

| Layer | What it can establish | What it does not supply |
|---|---|---|
| Lean kernel | The finite real-matrix implication, conservation, saturation, path propagation, and source-SCC coverage from explicit hypotheses | Actual substitution geometry or authentication of exported graph bytes |
| Quint | Independently specified exact finite models, deterministic transitions, and adversarial controls within stated bounds | An arbitrary-dimensional real-matrix proof or a universal strict-PIP theorem |
| Pinned Mojo and Python replay | The exact #515 finite graph, retained occurrence multiplicities, physical budget rows, source witnesses, and byte equality | A Lean proof that these executable objects realize every geometric premise |
| Refinement obligations | The explicit mapping between each certificate field and each formal hypothesis | Automatic discharge merely because a source digest or CI status matches |

The [refinement assessment](physical-mass-refinement-2026-11-08.md) gives the
source manifest and replay contract. Existing #515 counts and its historical
successful run are evidence for that exact revision. They are not receipts
for the new kernel revision. New exact-head and merge receipts are recorded
in the pull request and the dedicated workflow artifacts.

The Quint runner requires 20 named deterministic tests and six deliberately
weakened models to fail at their intended assertions. Its finite quantifiers
cover 11,664 two-vertex integer tuples, all 512 directed three-vertex graphs
(loops included), 4,096 graph/loss-set pairs, and 32,768 graph/loss-set/known-set
triples. The last check excludes a proper stable propagated zero set under
source loss. These are domain cardinalities, not random execution counts.
Both local evaluator backends agree on the accepted model. The
[Quint replay record](../evidence/physical-mass-kernel-2026-11-08/QUINT-REPLAY.md)
retains the unsuccessful helper formulation and exact source-bound logs.

## Independent replay

The repository compiler and Mathlib pins are unchanged. From the repository
root, run the complete compiled-declaration audit and independent finite model:

```bash
./tools/setup_lean.sh
export PATH="$HOME/.elan/bin:$PATH"
./tools/check_lean.sh
python3 tools/check_physical_mass_quint.py --output /tmp/physical-mass-quint
```

The native source is deliberately checked out separately at its exact
revision. On a machine provisioned with the repository's pinned Pixi version:

```bash
git fetch origin 51dd090a6aefeb92210410a3f7e20d51926d7e86
PSC_MASS_SOURCE=$(mktemp -d)
PSC_MASS_OUT=$(mktemp -d)
git worktree add --detach "$PSC_MASS_SOURCE" 51dd090a6aefeb92210410a3f7e20d51926d7e86
(cd "$PSC_MASS_SOURCE/kernel" && pixi run --locked mojo run -I . tests/test_c4_overlap_physical_mass.mojo)
(cd "$PSC_MASS_SOURCE/kernel" && pixi run --locked mojo run -I . c4_overlap_physical_mass.mojo) > "$PSC_MASS_OUT/physical-native.txt"
python3 "$PSC_MASS_SOURCE/oracles/python/c4_overlap_physical_mass.py" > "$PSC_MASS_OUT/physical-oracle.txt"
python3 tools/check_physical_mass_refinement.py \
  --source "$PSC_MASS_SOURCE" \
  --native "$PSC_MASS_OUT/physical-native.txt" \
  --oracle "$PSC_MASS_OUT/physical-oracle.txt" \
  --output "$PSC_MASS_OUT/source-receipt.json" --self-test
```

The [dedicated workflow](../.github/workflows/physical-mass-kernel.yml) runs
these layers on the exact PR head and again on the main merge revision. Its
artifacts identify the kernel commit/tree separately from the #515 source
commit/tree. The compiled audit rejects local axioms, admitted proofs and
nonstandard transitive axioms; the allowed Lean axioms remain `propext`,
`Classical.choice`, and `Quot.sound`. The Quint runner uses an immutable
private source snapshot and refuses a source or revision change during replay.

## Adversarial boundaries

All six required failures are retained in the independent Quint model:

| Weakened check | Failure being tested |
|---|---|
| Conservative source SCC allowed | A nonzero overlap vector can remain on a conservative source |
| Losing sinks substituted for losing sources | Forward zero propagation cannot travel backwards from a sink |
| An occurrence omitted | The smaller matrix can have artificial deficit; the original overlap supersolution no longer belongs to that matrix |
| `Th` used instead of `Tᵀh` | The finite-sum pairing has the wrong orientation and the claimed zero conclusion can be false |
| Zero mass allowed | Weighted conservation alone need not force every supersolution slack coordinate to zero |
| Incomplete root reachability | Proving zero on the supplied subgraph says nothing about an omitted conservative component |

These are different logical failures. In particular, the omitted-edge and
incomplete-domain controls test source refinement. They do not refute the
correct conditional theorem about a supplied matrix. The zero-mass control
tests the saturation step; it is not advertised as satisfying every other
assumption of the final source-loss theorem.

## Practical next condition for issue #461

The finite algebra reduces the next research condition to a concrete
structural statement:

> On a complete, geometrically realized overlap carrier for a supplied
> finite strict-PIP system, every inverse source SCC contains a genuinely
> omitted positive physical interval.

Equivalently at the certificate level, no inverse source component may be
conservative under the authenticated physical subdivision. This condition
is already executable for #515's twelve sources. A uniform proof would
need to derive it from actual ordered occurrences, strict child closure,
and the relevant Pisot/recognizability hypotheses. Finiteness by itself
does not exclude a conservative component, and testing larger finite
families cannot replace that derivation.

For mixed track-swap orbits, the refinement must preserve
`m_i T_ij = m_j F_ji` and use the weighted mass `H_i = m_i h_i`.
The size-two simplification in #515 cannot be transferred unchanged.

There are still two distinct geometric steps. One must construct a complete
finite carrier for the desired system and justify its overlap
supersolution. One must also turn its null-overlap conclusion into the
**actual one-step interior zero-return newborn** with the required
`Sync_+` or `Sync_-` neighbor demanded by
[issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461).
Zero measure does not mean an overlap set is empty and supplies no ordered
cut location by itself. These obligations are not consequences of the
matrix lemma.

## Claim status

No governed C4 or PSC status is promoted by this contribution. General
conservative-class exclusion, the geometric realization/refinement, the
one-step newborn bridge, and PSC remain open. Independent human review is
separate final validation debt under the repository policy and is not an
additional premise of this conditional proof.
