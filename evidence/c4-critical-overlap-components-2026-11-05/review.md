# Review record for the SCC obstruction target

**Review type:** separate AI-agent mathematical/source review, plus the
focused controls described below. This is not independent human review,
Lean formalization or a substitute for exact execution receipts.

## Written proof and prior art

The targeted gate inspected four primary sources before implementation.
The proof review checked CE1–CE6, row-to-child orientation, the strict
proper-ancestor comparison in the classical Frobenius–Victory theorem,
construction and uniqueness of the eigencone rays, incoming-equation
counterexample, scaling under positive upper bounds, and the minimal
polynomial exclusions. It returned GO with no blocking defect.

The review requested explicit authentication of minimality for the degree
shortcut. The accepted note states this requirement and retains the
counterexample `theta=2`, `g(t)=(t-2)(t-3)`, `A=[2]`.

## Native source review

Read-only review of `kernel/psc/c4_overlap_scc_obstruction.mojo` returned
GO at SHA-256
`916f969629bab10750a281d510e886bf7c7b16cee4122d85085b2e6c9a3c4763`.
It checked SCC and complete-source reconstruction, retained multiplicities,
authenticated cubic minimality and root isolation, positive spectral
witness validation, vendored `Fp` bounds/rejection, sparse polynomial
evaluation, elimination bookkeeping, safe zero propagation and refusal
semantics. The reviewer made no edits and did not duplicate native
compilation; command execution is recorded separately.

## Oracle defect, repair and second review

The initial oracle cached a mutable `Graph` and returned the same object.
Review reproduced a substantive defect on source 0: after replacing all
21,151 returned occurrence edges by empty rows and recomputing the SCC
report, source authentication accepted the altered graph because the
expected reference had been mutated too.

The accepted implementation caches immutable source snapshots and JSON
analyses, returning defensive reconstructions. The reviewer repeated the
attack: it now raises `actual complete occurrence graph mismatch`, and
a fresh source-0 graph still has 21,151 edges. Mutating a returned report
also leaves the reference unchanged and is refused. Regressions retain
both attacks. All accepted certificate data are reauthenticated with the
repaired verifier.

The second review found no further substantive defect in supported
acceptance paths. It checked exact integer matrix guards, Boolean-witness
refusal, independent SCCs, polynomial minimality, integer-power evaluation,
transposed modular elimination, witness signs/identities and complete
record comparison. Focused rational controls returned `(False,False)`
for the outgoing-forced subcritical case, `(True,True)` for the
supercritical-ancestor case and `(False,True)` for critical ancestry.
The full twelve-source replay belongs to the separate parent execution.

## Remaining boundaries

No review identifies feasible eigenvectors with actual positive overlap
measure, promotes arbitrary modular singularity to Perron criticality,
or imports tiling/Meyer/degree-one hypotheses from the literature.
The new finite computation recovers the existing twelve-source result by
a different certificate and does not enlarge the source class. Independent
human mathematical review remains pending as validation debt.
