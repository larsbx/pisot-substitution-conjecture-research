# Bounded source-bound target witnesses — 2026-11-08

**Parent:** PR #520 at `0b27766012f56c0ab0f3db3740021d9e0e1f2f97`.
**Scope:** quantitative formal refinement of the existing complete-support
rank certificate, not finite BPA extraction or a general Pisot theorem.
The earlier sources and shared append-only correction ledger are preserved.

## Work shown

### Assumptions and hypotheses

The independently specified `actual`, `stateOK`, and `target` functions
remain authoritative. An accepted finite rank packet must match every
literal ordered child row, including exits and multiplicities, and supply
at least one STRICTLY lower-ranked child at each nontarget state. Ranks
are natural numbers. A target is the actual one-letter diagonal, not a
packet-supplied success flag. These are exactly #520's original hypotheses.

The two certificate families may use different finite index sets and may
alias raw states. Their compatibility theorem assumes the SAME raw source
children, source-state domain and target predicate, not merely the same
printed index or independently chosen target flags.

### Derivation / reduction

`R1RankWitness.lean` introduces an exact-length child path `Steps`. Strong
induction on the start rank gives a target path with `k <= rank(start)`:
if the state is already a target, choose k=0; otherwise choose a strictly
lower-ranked actual child, take its induction witness, and add one edge.
Complete row equality transfers that witness to the raw source relation
WITHOUT changing k. The theorem bounds ONE selectable path. A different
actual path may take longer or avoid the target forever.

The new certificate incompatibility theorem uses #520's arbitrary-path
strict-support soundness: a selected strict raw state cannot also belong
to an accepted all-state rank carrier for the same source specification.
This works with different index sets and duplicated raw-state decodings.

Two concrete consequences are staged in Lean: every state in the complete
`0->01,1->0` fixture has a target path of length at most one, and NO assignment
of arbitrary natural ranks can make the complete binary negative fixture
pass rankCheck. The latter is an unbounded symbolic statement, not the
finite 0..3 rank search used for calibration.

Quint imports the existing pure literal-source checker and fixture data,
then deterministically selects the first lower-ranked child in actual row
order. Its separate witness replay checks the root, every edge, strict
rank decrease, the bound, and the true endpoint. The Lean proof establishes
existence and length of a source path; it does not prove a full compiler or
extractor refinement for the particular Quint implementation.

### Evidence and replay

- New Lean module: `proof/psc_routes/R1RankWitness.lean`, seven named theorem
  declarations and an exact qualified-name axiom audit.
- New Quint module: `proof/quint/PscR1RankWitness.qnt`, nine named deterministic
  tests and a dependency on the unchanged `PscR1SupportCertificate.qnt`.
- New exact-head workflow: `.github/workflows/psc-r1-rank-witness.yml`; it
  compiles all source dependencies, requires their existing receipts and
  all seven new receipts, and requires every named Quint test to execute.
  Two independently typechecked mutations must fail the intended tests:
  replace strict rank decrease by non-strict decrease; omit the endpoint
  target check. Neither a parse error nor an empty test run is evidence.

Independent local finite replay reconstructed the original literal rows
and checked 224 witnesses (four roots for each of the 56 accepted ranks
among {0,1,2,3}^4). Exactly 112 traces have length zero and 112 length one.
It rejected all 1,024 rank assignments in {0,1,2,3}^5 for the binary negative
fixture, seven malformed/misbound traces, and discriminated both new
mutations. The replay script is an attachment oracle, not a Python-only
canonical repository implementation. Local Lean and Quint are unavailable;
no new formal-runtime receipt is claimed.

### Negative controls

The source graph retains the off-diagonal `plus -> minus -> plus` cycle.
A complete all-state rank certificate can coexist with that avoiding walk;
a witness with more edges than the initial rank is not the promised bounded
witness, even when it eventually reaches a target. Replacing `<` by `<=`
incorrectly admits equal-rank target-free cycles. Omitting the endpoint
check incorrectly admits the zero-edge trace of a nontarget root. An edge
to a real target is still invalid when it is absent from the actual child
row; a trace starting at a different raw root does not prove the requested
root productive. Empty and out-of-range traces must be refused.

### Non-claims / remaining gaps

No finite all-Pisot carrier is constructed; no uniform rank or target path
inside an arbitrary strict PIP component is established. No claim about
all-walk termination, source completeness from a cap, PSC, C4, BH, A1', G1
or PDS is promoted. Canonical Mojo packet extraction and exact source
refinement remain separate acceptance obligations. Independent human
validation remains after closure, not a present blocker.

## Targeted dependency decision and session evidence log

**Proceed as refinement of an already reviewed contract.** The induction
is the quantitative version of #520's `rank_progress_productive`, not a new
mathematical mechanism. Its existential/all-walk distinction is already in
`c4-ordered-word-completion-interface-2026-11-02.md` section 3 and the
corrected #516/#518 productivity note. This continuation does not reopen a
retired universal monotonicity argument or assert new prior-art novelty.

- 2026-11-08: At parent head `0b277660...`, workflow 42467642973 executed all
  twelve named support-certificate Quint tests and rejected both intended
  coverage/quantifier mutations. Its Lean job 128690751675 failed BEFORE
  compilation during pinned elan download, after six HTTP 504 responses.
  This is a provisioning failure, not a failed theorem or a Lean pass.
  A targeted rerun was requested; do not inherit its outcome at a new head.
- 2026-11-08: Strict rank decrease, actual edge membership, source-root
  identity and a real target endpoint are separately necessary parts of a
  bounded witness check. The new finite controls distinguish all four.
  The structural correction is already recorded by #516/#518/#520; this
  file records the quantitative extension without rewriting that history.
- Latest-head hosted compilation, Quint execution and mutation receipts
  remain required. Source declaration counts and this finite local oracle
  are not substitutes for them. No merge is authorized by this note.


## Decidability repair follow-up

The bounded raw-witness proof uses the same proof-recovery boundary as the
base checker. The [repair acceptance note](psc-r1-decidability-repair-2026-11-08.md)
documents the shared computable instance correction and the full four-module
compiled inspection gate. Current exact-head receipts are recorded in PR #520;
earlier pending evidence remains historical rather than inherited acceptance.
