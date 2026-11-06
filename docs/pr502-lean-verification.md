# PR #502: dedicated source-word Lean verification

Scope: the two literal run families merged at
`56ecd728069465c6c0e58e4d53936d6bce986e1f`.
This development is separate from PR #500 and imports no overlap-certificate
module. Governed theorem statuses, generated Proof Bank, and the general PSC
claim are unchanged. This branch is for review; do not merge automatically.

## Work shown

### Assumptions and hypotheses

Words are finite lists over an explicit three-constructor alphabet. Parikh vectors
are exact natural-number letter counts. A witness consists of two equal-Parikh
prefixes followed by the same literal letter. The source substitutions are
nonerasing. Parameters are natural numbers; no enumeration bound is a hypothesis.

### Derivation / reduction

The core proves Parikh preservation, witness propagation under inflation,
propagation to any later generation, and the implication from pairwise
generation-n witnesses to a singleton diagonal with balanced prefix and suffix
in every nonempty balanced root's complete n-th inflation.
No irreducibility, Pisot property, geometric representation or finite closure
assumption is needed for these word lemmas.

### Evidence and replay

Implementation is being developed. No Lean kernel acceptance is claimed until
the dedicated exact-head workflow passes. The session has no local execution
environment. Reproduce from a clean exact checkout with the pinned toolchain:

```sh
bash tools/setup_lean.sh
export PATH="$HOME/.elan/bin:$PATH"
python3 tools/check_two_tail_502_lean.py --expected-revision FULL_COMMIT_SHA --output /tmp/pr502-lean
python3 tools/make_proof_bank.py --check
```

The runner records source hashes, compiler version, commands, complete build
and axiom logs. It rejects dirty/wrong revisions, proof escapes, nonstandard
axioms and source changes. Finite controls use kernel-reduced `decide`, never
finite enumeration as evidence for an unbounded theorem.

### Negative controls

The large-b tail-102 formula must be rejected at b=2. Separate fourth-level
certificates are required at b=1 and b=2. Tests will also pin sharpness of the
source-pair bound; root minimality is a different claim.

### Non-claims / remaining gaps

Pending: kernel acceptance of the generic lemmas, parameter-dependent word
identities and their prefix inclusions, both boundary families, exceptions,
the b=2 rejection and the assembled infinite-family theorem.
No axiom or placeholder proof closes these obligations. Existing #502 Python
controls are independent historical evidence and are not credited as Lean proofs.
This contribution asserts neither arbitrary-family coincidence nor PDS, finite
BPA termination, C4 in general, or PSC.

## Targeted prior-art / stop-go check

This formalizes the already reviewed written contract of #502, not a new
universal diagnostic. Read #502's word proof §§3–8 and §11 and the existing
`docs/pds-strong-coincidence-literature-gate-2026-10-04.md` before implementation.
Barge–Diamond (2002, DOI 10.24033/bsmf.2433) supplies the equal-prefix-abelianization
terminology. Akiyama–Lee (2014, arXiv:1403.0377), Definitions 3.1–3.3 and
Corollary 4.5, is the existing source-spectrum boundary audit, not a premise
of this word proof. Sirvent–Starosta (arXiv:1711.10167) concerns different
substitutions and supplies no same-source counterexample to these identities.
Decision: proceed with the exact two-family word specialization; import no
strong-coincidence-to-PDS theorem. No new novelty or literature-completeness claim.
