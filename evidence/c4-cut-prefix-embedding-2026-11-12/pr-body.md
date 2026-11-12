## Summary

The accepted archived-graph results prove nullity on their stated rooted domain. Connecting a hypothetical strict obstruction to positive overlap measure still requires an authenticated link from actual balanced cuts to the original prefix tiles. This change formalizes the literal embedding and uniform approximation step of that link.

For either original source `1/021/001` or `1/012/001`, fix a finite word `u`. Every actual marked position of `sigma^(12n)(u)` has a same-letter prefix witness in that source's own authenticated infinite word. Its stable error is at most `(7/8)^n C_{s,u}`, with a bound fixed by the uninflated source, and its residues agree exactly at every depth `q <= 12n`. Two marks at a balanced cut obtain witnesses around the same exact cut vector.

Adds **37 named Lean proof declarations** across `CutPrefixEmbedding`, `NamedCutProximity`, and `CutPrefixControls`, canonical Mojo witness construction, an independent complete-packet Python oracle, and focused replay CI. The proof bank is regenerated; all 126 governed claim statuses remain unchanged.

Tested code: `73a0b6a95539beb1b6712afec0f8412571b41cd3`

Tree: `8233701f593a8ba680356a88c2c6fc8e4cf01df5`

Base: `main@9a1357ed5dae3b4502d29c34396d0e9403ccca75`

**The complete local isolated Lean build and compiled axiom audit passed at the tested code revision.** The later evidence-only commit archives that result without claiming a fresh build of itself. Finite replay and bounded Quint checks retain their separate scope. Hosted candidate CI and complete hosted locked-environment acceptance remain pending.

## Work shown

### Assumptions and hypotheses

The generic embedding requires actual parent/local marks, proved occurrences of their parent letters in the same reference word, and that word's fixed-prefix identity for the chosen substitution power. It retains both complete literal marks, following letters, and source-minus-reference orientation.

The named specialization supplies these premises from the existing period-two words and uses powers `12n`, the original stable chart, the original matrix-adic factor, and the proved block-twelve `7/8` contraction. The two words are not identified through their equal incidence matrices. Strict-cut label separation additionally requires actual membership in a supplied `StrictSystem`.

### Derivation / reduction

Write an inflated marked prefix as `X = sigma^k(u_<i) P`. Re-embed its identical local mark after an authenticated occurrence of its parent letter, with reference prefix `Y_d`, giving `Y = sigma^k(Y_d) P`. Literal cancellation proves

```text
p(X) - p(Y) = M^k (p(u_<i) - p(Y_d)).
```

Projection gives `x* - y* = A^k z*`. Image-lattice membership and the genuine quotient reduction maps give exact residue equality at every `q <= k`. A finite sum over original source positions and the three fixed reference choices bounds every correction independently of `k`.

At `k = 12n`, the existing contraction yields the stable error bound. The uniform conclusion has the order `forall epsilon > 0, forall q, exists N, forall n >= N, forall actual marks, exists a same-letter prefix witness`. Actual prefix points belong to their corresponding tiles. Balanced prefixes share one Parikh vector; `StrictSystem.cut_follow` separately supplies distinct following letters for strict cuts.

### Evidence and replay

| Gate | Observed result |
| --- | --- |
| New Lean modules | All three passed the complete isolated source build, including `strict_cut_labels`; 37 explicit theorems and seven definitions matched their compiled records. |
| Independent Lean controls | All 15 controls passed the isolated build and compiled audit; only the permitted standard axioms occur. |
| Canonical Mojo replay | Passed full witness generation and 19 refusal controls. |
| Independent Python replay | Eight tests passed with native comparison enabled and no skips; optimized-mode oracle compared every packet field and record. |
| Existing named-chart Quint suite at candidate head/tree | Passed 22 bounded tests and rejected 10 mutations. |
| Existing prefix-window Quint suite at candidate head/tree | Passed 19 bounded tests and rejected nine mutations. |
| Complete isolated source build and compiled axiom audit | **Passed, exit 0.** All 2,670 source-named proofs reached; 6,589 compiled declarations and 4,819 theorem constants checked. Only `propext`, `Classical.choice`, and `Quot.sound`. The initial dependency-extraction `ENOSPC` failure is preserved separately. |

The native packet contains **3,220 complete marked witnesses, 21,028 residue witnesses, and 272 balanced cuts**, including 51 cuts with distinct following letters. Its 2,060,008 bytes have SHA-256 `440127dd5d0617cc1f3b75a960db4fbde7e7c31cc931146a1635637a967b030e`. The finite domain is both fixtures, powers `0,2,4,6`, sources `012`, `2010`, `120`, and paired controls `01/10`.

Local native replay used the exact lock-matched compiler `Mojo 1.1.0.dev2026090805 (34562fa1)` from an existing auxiliary environment. Complete local `pixi install --locked` provisioning failed on a network dependency download, so full locked-environment or hosted-native acceptance is not claimed. The focused workflow will provision that environment on the published candidate.

The oracle independently expands literal words, locates parent blocks, recounts prefixes, and uses unbounded integer incidence action. Acceptance compares the full nested packet, including types, inventories, order, source identities, complete marks, corrections and all residues. Finite replay is not the quantifier domain of the Lean convergence theorem. The unchanged Quint suites remain bounded checks of their own model interfaces.

Replay from the repository root:

```sh
python tools/make_proof_bank.py --check
./tools/setup_lean.sh
./tools/check_lean.sh
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_cut_prefix_embedding.mojo)
(cd kernel && pixi run --locked mojo run -I . c4_cut_prefix_embedding.mojo) > /tmp/cut-prefix-packet.json
python -O oracles/python/c4_cut_prefix_embedding.py --native /tmp/cut-prefix-packet.json --controls
C4_CUT_PREFIX_NATIVE=/tmp/cut-prefix-packet.json python -m pytest --assert=plain -o addopts='' -q tests/test_c4_cut_prefix_embedding_oracle.py
```

The focused workflow checks out and records the exact head/tree, compares the complete native packet, and retains receipts. The existing overlap Lean workflow supplies the complete isolated build and compiled audit.

### Negative controls

Lean controls preserve distinct actual words despite equal incidence, reject a one-step fixed-word substitution, exhibit a nonzero signed correction, and prove that finite residue agreement need not extend to the next depth or imply equality in the inverse limit. A shrinking coefficient with depth-growing corrections has constant error one, demonstrating why the source bound must remain fixed.

Native and oracle controls reject source/reference substitutions, wrong parent or local marks, reversed corrections, altered prefix vectors, incomplete/corrupt residues, unequal paired cuts, dropped/duplicated/reordered records, and ambiguous JSON. Valid native mutation baselines are verified outside rejection-catching blocks. Unsupported powers, invalid letters, terminal positions and resource exhaustion refuse construction. The oracle's 19 controls comprise 18 refusals plus one residue sanity control.

### Non-claims / remaining gaps

This implements the literal embedding and uniform-proximity step of the written M1 argument. The remaining analytic assembly must:

1. Use compactness to turn simultaneous approximation into eventual containment in suitable open covers of the tile intersection.
2. Prove the fixed-origin regular-cylinder lattice count with the correct product normalization and covolume.
3. Combine a literal strict-cut density lower bound with the limit and outer-cover argument to derive positive product-Haar measure.

Proximity does not establish finite-depth membership in the intersection, and finite residue agreement does not establish positive measure. No all-packet identification, general PIP construction, C4, A1', BH, G1, PDS or PSC conclusion is promoted. The separate ordinary one-step ancestry work is not a dependency. Independent human review remains pending.

The complete local archive is `evidence/c4-cut-prefix-embedding-2026-11-12/`: it includes the losslessly compressed full native packet, full isolated log, all Quint logs and receipts, independent compiled-audit inspection, source hashes, and preserved failed/interrupted attempts. The compact-cover follow-on plan identifies an existing Mathlib route without adding a new formal claim. Later density must count original cut vectors; reference witness ordinals need not be injective.

Detailed derivation and source gate: `docs/c4-cut-prefix-embedding-2026-11-12.md` and `docs/c4-cut-prefix-embedding-literature-2026-11-12.md`.
