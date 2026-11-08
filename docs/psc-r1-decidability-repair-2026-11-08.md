# R1 certificate decidability repair — 2026-11-08

**Repair baseline:** PR #520, `aa8951221f4d3f80336efc9dc104e06018ba32d0`.
**Scope:** repair elaboration and verify the existing finite certificate
contract. No strict-support, progress, source-completeness or PSC hypothesis
is weakened. This is a regression repair of the already documented contract,
so the repository's literature gate does not require a new research review.

## Work shown

### Assumptions and hypotheses

The authoritative inputs remain `actual : Raw → List Raw`,
`stateOK target : Raw → Bool`, and `[DecidableEq Raw]`. A packet supplies only
finite decoding, indexed rows, and a support mask or natural ranks. The
strict predicate still requires a nonempty support, source admissibility,
literal ordered row equality, target exclusion, and closure under every
listed child. The rank predicate still requires source admissibility and
complete literal rows at every represented state, plus either a target or
one strictly lower-ranked child. These two proposition definitions are
unchanged.

`actual` is an independently supplied source specification, not a predicate
whose truth a packet may choose. The concrete binary and Fibonacci fixtures
recompute literal children from substitutions. None of this proves a finite
complete carrier exists for an arbitrary PIP substitution.

### Derivation / reduction

The failure was at **proof recovery**, not at the original finite Boolean
decision procedures. The two definitions used

```lean
@decide (StrictConditions actual stateOK target decode rows keep)
  (by unfold StrictConditions; infer_instance)
```

and its rank analogue. Those explicit instance arguments elaborate after
unfolding the proposition. They are not registrations of instances for later
callers. In the soundness proofs, `of_decide_eq_true hcheck` requires its own
implicit `[Decidable p]`. Typeclass search does not unfold these ordinary
proposition definitions to reconstruct the decision procedure. Therefore the
successful local construction inside `@decide` does not satisfy that later
instance search. Lean's own signature is
`of_decide_eq_true [Decidable p] : decide p = true → p`.

The pinned compiler source confirms both pieces: [`Init/Prelude.lean`](https://github.com/leanprover/lean4/blob/6a10ac8c22beadecabdbb0919c2b50214762f91d/src/Init/Prelude.lean)
defines that implicit instance argument, and
[`Lean/Meta/SynthInstance.lean`](https://github.com/leanprover/lean4/blob/6a10ac8c22beadecabdbb0919c2b50214762f91d/src/Lean/Meta/SynthInstance.lean)
uses `.instances` transparency. The corresponding
[`Lean/Meta/Basic.lean`](https://github.com/leanprover/lean4/blob/6a10ac8c22beadecabdbb0919c2b50214762f91d/src/Lean/Meta/Basic.lean)
definition unfolds reducible and instance definitions, not ordinary
semireducible proposition definitions.

The correction registers `strictConditionsDecidable` and
`rankConditionsDecidable`, with the same `unfold ...; infer_instance`
construction. Both executable checkers now use `decide` with those shared
instances. The same construction is available to all three original
soundness calls and to the downstream `rankCheck_bounded_raw_witness` call.
The theorem statements and proof bodies need no replacement.

Decidability remains finite and computable. No `classical`, `noncomputable`,
`sorry`, additional assumption, or new axiom is introduced into either
checker or instance. The pre-existing general rank-induction proofs may
reason classically about an arbitrary target predicate on an arbitrary type;
that proof reasoning is separate from the executable finite validators.

The validator section also gives local priority to Lean core's
`Nat.decidableForallFin` and `Nat.decidableExistsFin`. This makes the finite
index enumeration explicit in instance selection instead of using Mathlib's
generic `Fintype` decisions and their additional proof transports. It does
not change the conditions, their quantifiers, or any theorem proof body.

**Executability and axiom closure are different checks.** A transitive axiom
inventory includes erased proof dependencies. The presence of
`Classical.choice` there does not by itself mean a Boolean program cannot
execute. The stricter checker budget here deliberately excludes it in both
computation and associated proof terms, while the fourteen `#eval` assertions
separately verify actual execution. The pinned core's bounded Nat decision
roots are marked `noncomputable` to force their proved `@[csimp]`
tail-recursive runtime replacements; this implementation detail is also not
evidence of a classical runtime decision procedure. The source comments and
definitions are in [`Init/Data/Nat/Lemmas.lean`](https://github.com/leanprover/lean4/blob/6a10ac8c22beadecabdbb0919c2b50214762f91d/src/Init/Data/Nat/Lemmas.lean).

### Evidence and replay

The failed baseline is preserved as historical evidence:

- [Support workflow 42471186365](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/42471186365),
  Lean job `128702057575`: toolchain provisioning succeeded, then compilation
  failed at lines 142, 184 and 210 in `of_decide_eq_true` calls. The axiom
  audit rejected `sorryAx` in `strictCheck_sound` after elaboration recovery.
  No accepted support-theorem receipt follows from this run.
- [Rank workflow 42471186399](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/42471186399),
  Lean job `128702055580`: six elan-download HTTP 504 responses; compilation
  was skipped. Its Quint job passed. This provisioning failure is a separate
  observation from the support source-compilation failure.

The first repair candidate, `4636ecb78bd1e650c9b895b0ed094ccc97303f72`,
then passed all four module compilations, all 47 compiled theorem inspections,
all fourteen executable assertions, and the 21 hosted Quint tests with four
mutants. [Support run 42517853797](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/42517853797)
succeeded. [Rank run 42517853730](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/42517853730)
was correctly withheld by the additional strict checker axiom budget:
`strictConditionsDecidable` had a transitive `Classical.choice` dependency.
That was not an admitted proof, a failure of the original mathematical
contracts, or a failure to execute. The scoped core-instance priority above
addresses the stricter proof-dependency requirement without relaxing it.
The diagnostic now calls this an exceeded axiom budget rather than inferring
noncomputability from transitive proof dependencies.

The corrected rank workflow compiles, in a fresh output directory:

1. `R1ProductivityScope` — 15 original named theorems;
2. `R1SupportCertificate` — 12 original named theorems;
3. `R1SupportFixtures` — 13 original named theorems;
4. `R1RankWitness` — 7 original named theorems.

It then imports the compiled chain into `R1SupportAcceptance.lean`. This
separate acceptance module checks generic computable instance synthesis,
executes fourteen positive and rejecting Boolean fixture checks, checks the critical
theorem types against their stated contracts, and prints the actual compiled
types and axiom sets of all 47 theorems. Unexpected axioms, including
`sorryAx`, are refused. The computational definitions are checked separately
from the theorem whitelist, so allowing classical reasoning in a theorem
does not authorize classical choice in certificate validation.

Replay after `./tools/setup_lean.sh`, from `proof/PscVerif`:

```bash
set -euo pipefail
routes="$(cd ../psc_routes && pwd)"
out="$(mktemp -d)"
for module in R1ProductivityScope R1SupportCertificate R1SupportFixtures R1RankWitness; do
  lake env bash -c 'export LEAN_PATH="$1:${LEAN_PATH:-}"; exec lean --root="$2" -o "$1/$3.olean" "$2/$3.lean"' _ "$out" "$routes" "$module"
done
lake env bash -c 'export LEAN_PATH="$1:${LEAN_PATH:-}"; exec lean --root="$2" "$2/R1SupportAcceptance.lean"' _ "$out" "$routes"
```

Both dedicated workflows bind checkout to the PR head. The bounded-witness
artifact additionally records all affected Lean source hashes, dependency
pins, workflow hash, compiler versions and compiled-object hashes. The PR
receipt table records the actual corrected revision and hosted run IDs after
completion; successful source inspection alone is not a kernel receipt.

The local executor installed the pinned release but denied the numeric
`/proc/<pid>/exe` lookup used by Lean's `IO.appPath`; the unmodified executable
therefore failed before compilation with `failed to locate application`.
That local environment failure is not credited as Lean verification. The
hosted jobs run the unmodified pinned compiler and provide acceptance.

### Negative controls

The unchanged support Quint model has twelve named deterministic tests and
two independently typechecked semantic mutants: missing literal source
coverage and requiring every edge to decrease. The unchanged bounded-witness
model has nine named tests and two more mutants: non-strict rank decrease
and missing target-endpoint validation. A mutant must fail its designated
semantic test; a parser failure, type error or empty test selection is not
accepted as detection.

The witness controls retain actual-edge membership, source-root identity,
strict decrease, path length bounded by the initial rank, and an actual
target endpoint. They reject empty and out-of-range traces. The positive
fixture still permits a target-avoiding cycle on unchosen edges. The strict
fixture still detects omitted diagonal exits, changed order or multiplicity,
and an empty support. Critical compiled contract checks reject replacing the
desired propositions with trivial conclusions or adding contradictory
premises.

### Non-claims / remaining gaps

Keep four evidence levels separate: source-level reasoning; successful
kernel compilation with inspected statements and axioms; independent bounded
Quint execution and mutation discrimination; and completeness of the
substitution system to which a packet is attached. A pass at one level is not
an automatic pass at another.

The Quint runs use the declared binary-word fixtures and their supplied
two-image substitution tables. They do not establish total admission for
arbitrary integer-encoded words or a general Lean–Quint refinement theorem.

The quantitative theorem establishes **one** actual target path of length at
most the starting rank. It does not bound all walks. Incompatibility requires
the same raw state and source specification, even when the two packets use
different index sets or aliased decoding. The binary no-rank result quantifies
over arbitrary natural ranks for that concrete source fixture; its validity
does not depend on a finite rank search.

Finite PIP support extraction, canonical Mojo packet production, a general
source-bound target-path argument, and refinement of the particular Quint
selector remain separate obligations. PSC, C4, BH, A1′, G1 and PDS status is
unchanged. Independent human review remains post-closure validation debt.
