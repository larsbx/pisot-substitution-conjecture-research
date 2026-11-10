# R1 adversarial correction: productivity is backward, not forward

Baseline: R1 PR #507 at `f5b6625d0d6bd33ee8f3f07289cdc23e0911dc11`.
Status: exact written negative control, independently replayed finite arithmetic;
Lean and Quint sources staged, **not yet compiled/executed at the new head**.
This changes no PSC/C4/BH/A1′/G1 classification.

## Work shown

### Assumptions and hypotheses

Productivity of a balanced-pair state means that **some** descendant is a
one-letter diagonal pair. Strict nonproductivity means **no** descendant is a
one-letter diagonal. These are different quantifiers. A proof that a root is
productive does not imply that every descendant, or every reachable recurrent
component, is productive.

The present control uses the literal binary substitution

```
0 -> 01
1 -> 10
```

Its incidence matrix is `[[1,1],[1,1]]`, positive but singular, with characteristic
polynomial `x(x-2)`. It is outside the standing irreducible-characteristic PIP
hypotheses. This is a counterexample to the **unrestricted graph/source inference**,
not to PSC or any theorem that separately proves the missing PIP implication.

### Targeted prior-art stop/go

The repository already separates existential target reachability from exclusion
of every avoiding path in `docs/c4-ordered-word-completion-interface-2026-11-02.md`
§3. Its proper-prefix, ordered-child and raw-orientation contracts are retained.
`docs/c4-orientation-monodromy.md` supplies a distinct primitive non-PIP strict
control; no novelty is asserted for the logical distinction or binary substitution.
**Proceed narrowly:** formalize a fully literal legal-factor regression and correct
the latest R1 scope claim. Do not add a new finite census or substitute this
non-PIP control for the still-missing irreducible-Pisot argument.

### Derivation / reduction

Let `R=(001,100)`, `A+=(01,10)`, and `A-=(10,01)`. Both words of R occur in the
same literal third iterate `01101001`: `001` at positions 5..7 and `100` at 4..6.
Their Parikh vectors are equal. Their only balanced cuts are 0 and 3, so R is
irreducible.

The **complete ordered irreducible factorization** is

```
σ(001) = 01 | 0 | 1 | 10
σ(100) = 10 | 0 | 1 | 01
R -> A+ , (0,0) , (1,1) , A-
```

Every cut is found by equality of literal prefix letter counts. The full cut list
is `[0,2,3,4,6]`. In particular, the two diagonal children begin at balanced
prefixes, not merely equal physical positions with unequal Parikh residuals.

Yet the strict class is completely child-closed:

```
A+ -> A+ , A-
A- -> A- , A+
```

Both pairs are irreducible and noncoincident, and every child is one of those two
pairs. They reach one another; both also have a self-loop. Induction on arbitrary
finite descendant paths proves that neither can ever reach a diagonal. Thus R
is productive and has a literal descendant in a closed nonproductive recurrent
class. The complete closed graph including diagonal successors has five states:

| State | Full ordered child list |
| --- | --- |
| R | A+, (0,0), (1,1), A- |
| A+ | A+, A- |
| A- | A-, A+ |
| (0,0) | (0,0), (1,1) |
| (1,1) | (1,1), (0,0) |

The valid propagation direction is: a productive descendant makes its ancestors
productive. The converse is false. Excluding a **specific** SCC therefore requires
productivity or closure evidence on that SCC's own states, bound to complete raw
ordered factors. A reachable diagonal somewhere else in the root's graph is
insufficient.

### Evidence and replay

`proof/psc_routes/R1ProductivityScope.lean` contains fifteen scoped theorems. The
finite graph table is checked against an independent literal inflation-and-all-cuts
calculation for **every** state. `raw_child_coverage` rules out silently omitted
factor children. Strict nonproductivity is an induction on paths of arbitrary
length, not an enumeration to a fixed depth. The declaration inventory and
standard-axiom checks fail closed.

`proof/quint/PscR1ProductivityScope.qnt` reconstructs all five literal factor rows,
checks legality and irreducibility of R, compares both possible futures from R,
and rejects a truncated row that retains only the successful diagonal children.
Six tests are explicitly named and must all execute. List operations and index
selection use the pinned Quint 0.33.1 built-ins. The nondeterministic `step` retains
every child ordinal; the named tests themselves contain no nondeterminism.

The workflow `.github/workflows/psc-r1-productivity-scope.yml` checks exact HEAD,
fifteen Lean axiom receipts and all six named Quint test successes. It coalesces
superseded runs of this one workflow; it does not cancel unrelated research checks.
No new executable census or canonical Python kernel is introduced. A dependency-free
Python finite-word oracle was run in the working session as a secondary arithmetic
check, not as Lean/Quint acceptance.

Replay:

```
./tools/setup_lean.sh
(cd proof/PscVerif && lake env lean ../../proof/psc_routes/R1ProductivityScope.lean)
npx --yes @informalsystems/quint@0.33.1 typecheck proof/quint/PscR1ProductivityScope.qnt
npx --yes @informalsystems/quint@0.33.1 test --backend=typescript proof/quint/PscR1ProductivityScope.qnt --main=PscR1ProductivityScope
```

### Negative controls

The fixture is not PIP. Root source words are legal factors; their illegality
cannot explain the failure. No orientation is silently normalized. Keeping only
the diagonal children would falsely erase the strict class, so the truncated-row
negative test is mandatory. A bounded model run is not substituted for Lean's
arbitrary-path closure theorem.

### Non-claims / remaining gaps

This corrects the inference in the ledger-linked R1 boundary-localization note:
**the Tribonacci root is productive, so the root itself is not a strict
nonproductive state; its productivity alone does not classify all descendants
or the nine depth-six ancestry loops.** Their actual occurrence supports require
separate evidence. This control neither proves nor disproves strictness of any
of those nine Tribonacci loops.

The next reproducible R1 obligation is SCC- or occurrence-support-specific:
retain complete child lists, check the relevant support is child-closed, and
supply a diagonal path from a state **within that same purported strict support**.
Alternatively prove the PIP theorem that makes such a path unavoidable. Do not
infer descendant productivity from a productive root or promote a balanced
boundary to a diagonal without matching letters.

Human validation remains post-PSC. No merge is authorized by this correction;
new proof sources need exact-head hosted acceptance before kernel credit.
