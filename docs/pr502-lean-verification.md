# PR #502: dedicated source-word Lean verification

This development formalizes the exact two run families merged at
`56ecd728069465c6c0e58e4d53936d6bce986e1f`:

```text
0 -> 01, 1 -> 1^a 2 1^b, 2 -> 102
0 -> 01, 1 -> 1^a 2 1^b, 2 -> 120
a,b : Nat, 1 <= a+b
```

The standalone project is `proof/TwoTail502/`. It uses the existing repository's
Lean 4.34.0-rc2 and exact Mathlib dependency manifest, with only the project name
changed. It imports no PR #500 overlap code. Neither the existing Lean root
project nor governed theorem statuses or generated Proof Bank bindings change.

## Work shown

### Assumptions and hypotheses

`Word = List Letter`, with exactly three constructors representing 0,1,2.
`parikh w c = w.count c` is an exact natural-number vector.
Substitution is list flatMap; iteration and word powers are recursive exact
operations. A `Witness` exposes two actual equal-Parikh prefix words followed
by one common literal letter; an equal-mass formula alone is insufficient.

`DiagonalFactor` exposes a balanced prefix pair, a literal singleton (c,c),
and a balanced suffix pair in the complete inflated words. Balanced prefixes
have equal lengths. Thus the displayed singleton lies between consecutive
balanced cuts; factoring either surrounding balanced piece cannot split it.
The code does not implement a general BPA factorization algorithm.

### Derivation / reduction

| Module | Formal content |
| --- | --- |
| `Core.lean` | Exact words/Parikh vectors; substitution and iteration; Parikh preservation; nonerasing iteration; witness propagation to any later generation; pairwise witnesses imply balanced-root singleton-diagonal productivity |
| `Families.lean` | Literal sources; block identities F,G,H,U,V,W,X,Y,Z through level five; symbolic Parikh identities and closed polynomial vectors; fixed exceptions b=1,2; rejected large-b prefix at b=2 |
| `Prefixes.lean` | Actual prefix inclusions for a=k+1; all b, including b=0 and (a,b)=(1,0); a=0 tail-120 pairs at levels 3/4/5; a=0 tail-102 pairs at level 2 and the b=k+3 level-5 identity |
| `Theorem.lean` | Case split over arbitrary natural a,b; all pairwise source witnesses at generation 5; arbitrary nonempty balanced-root productivity |
| `Tests.lean` | Four literal exceptional-word prefixes; exhaustive earlier-cut rejection for the sharpness source; no smaller common source-pair bound |

The positive parameter is represented as `k+1`, and the large boundary parameter
as `k+3`. These are symbolic natural numbers of unbounded size. The b=0
tail-120 argument uses the general prefix-of-`V^k W` lemma, including k=0,
so (a,b)=(1,0) needs no unstated positivity premise.

The public conclusions are
`TwoTail502.uniform_pairwise_five`,
`TwoTail502.uniform_balanced_root_productivity`, and
`TwoTail502.no_smaller_common_bound`.
Only the last uses a finite explicit counterexample, (01,211,120), for sharpness.
The parameter-uniform conclusions use symbolic list algebra and natural-number
proofs, together with the two isolated exact exceptions, not parameter enumeration.

### Evidence and replay

**Kernel accepted:** exact source revision `889cb6ced1fae155481a0ab6e992189b408e7e1b`,
[hosted run 42215167661](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/42215167661).
All 99 named proofs passed the compiled axiom audit. The existing generated
Proof Bank consistency check passed unchanged (126 governed claims, 68 existing
main-project named proofs, 375 source openings). The 99 dedicated proofs are
audited separately and are not silently credited to a governed PSC claim.

Permanent review evidence:
[`validation.json`](../evidence/pr502-lean-2026-11-06/validation.json) and
[`axioms-from-hosted.log`](../evidence/pr502-lean-2026-11-06/axioms-from-hosted.log).
The validation record links the exact hosted receipt/build/audit artifact and
its server-reported SHA-256 digest. Earlier failed development runs remain
identified in that record.

Reproduce from a clean exact checkout:

```sh
bash tools/setup_lean.sh
export PATH="$HOME/.elan/bin:$PATH"
python3 tools/check_two_tail_502_lean.py --expected-revision FULL_COMMIT_SHA --output /tmp/pr502-lean
python3 tools/make_proof_bank.py --check
```

The runner requires a full matching clean revision, checks that both projects'
compiler/configuration/dependency pins agree, and copies only PR502 sources and
configuration into a fresh temporary project. No compiled PR502 artifacts enter
that project. Provisioned pinned upstream dependency artifacts and the pinned
Lean compiler remain explicit trust inputs. The caller should provision those
dependencies with the checked-in setup script.

The receipt records source/configuration/runner SHA-256 hashes, compiler version,
commands, all named proof declarations and the axiom-log digest. Build and axiom
logs are retained with the receipt. Every named proof is audited; permitted
axioms are only `propext`, `Classical.choice`, `Quot.sound`.
The runner rejects proof escapes, missing/duplicate audit output, changed pins,
source changes and checkout changes. There is no local-executor result in this
session; evidence comes from the dedicated hosted exact-head run.

### Negative controls

- `large102_mass` is valid even at b=2; `reject_large102_b2` proves that
  the claimed right prefix followed by 1 is NOT a prefix of the fifth image
  of source 2. This preserves the distinction between abelianization and
  actual word membership.
- b=1 and b=2 use different exact fourth-generation cuts (27 and 50).
  Their four displayed literal prefixes are separately kernel checked.
- The sharpness scan covers every proper prefix position and all three possible
  following letters. A general lemma converts any existential word witness into
  one of those finite cuts; the scan is therefore exhaustive, not heuristic.
- The invalid parameter pair a=b=0 does not satisfy the theorem's hypothesis.

### Non-claims / remaining gaps

All implemented source-word proof obligations listed above are kernel accepted
at the recorded exact revision; there are no placeholder declarations or
family-prefix assumptions in the two public uniform conclusions.
Repository-wide CI and independent human review are separate from this focused
acceptance. No all-repository green status is claimed.

These word proofs do not formalize the incidence polynomial/Pisot classification,
the conditional spectral estimate in #502 §9, a native Mojo port or an
implementation-refinement theorem for the Python compressed DAG.
They do not establish arbitrary-family coincidence, finite BPA termination,
pure discreteness, general C4/G1/BH/A1' or PSC. The sharpness claim concerns
source-letter witnesses; it does not assert that a balanced root needs five
generations. Independent mathematical review remains separate validation debt.
PR #503 remains a draft and is not merged.

## Prior-art / stop-go record

This formalizes #502's existing written contract rather than introducing a new
universal diagnostic. Before implementation, the #502 word proof §§3–8 and §11,
and `docs/pds-strong-coincidence-literature-gate-2026-10-04.md`, were read.
Barge–Diamond (2002, DOI 10.24033/bsmf.2433) supplies the equal-prefix-
abelianization terminology. The existing gate audits Akiyama–Lee (2014,
arXiv:1403.0377), Definitions 3.1–3.3 and Corollary 4.5, as a separate
source-spectrum boundary. Sirvent–Starosta (arXiv:1711.10167) concerns different
substitutions and supplies no same-source counterexample to these identities.
Decision: proceed with the exact two-family word specialization; import no
strong-coincidence-to-PDS implication. No new novelty or exhaustive-literature
claim is made.
