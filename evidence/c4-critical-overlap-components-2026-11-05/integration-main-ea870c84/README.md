# Exact replay after integrating updated main

Main advanced to `ea870c846f6575e51aaa78ef4659e533da636b0a` while the
SCC result was being published. It contains the merges of PRs #498, #484,
#486 and #496. The integration preserves their incoming files exactly;
the conflicts were confined to the research ledger and generated proof
inventory. The incoming main ledger is preserved byte-for-byte with all
PR #497/SCC entries appended, and both proof-bank outputs were regenerated.
The SCC proof, algorithms, workflow and tests are unchanged.

The integrated tested source is published at
[`647cd56e8bb79ca3de50c66906cec5fef3ee264b`](https://github.com/larsbx/pisot-substitution-conjecture-research/commit/647cd56e8bb79ca3de50c66906cec5fef3ee264b).
Its full tree `bfd53bd5575aaaa0ab677eb6af755fb3794e8195` equals the
locally executed tree. The published merge has parents
`11ca54a5b4ec827271f190e973b2564c00df31f5` and
`ea870c846f6575e51aaa78ef4659e533da636b0a`.

| Check | Integrated-source result | Receipt |
| --- | --- | --- |
| Canonical native regression | Exit 0; final contract reached | [native-test](native-test.receipt.json) |
| Full native driver | Exit 0; identical complete packet | [native-driver](native-driver.receipt.json) |
| Independent/adversarial oracle tests | 29 passed; native packet supplied | [oracle-tests](oracle-tests.receipt.json) |
| Independent full packet authentication | Exit 0; committed receipt equality | [native-parity](native-parity.receipt.json) |
| Governance | All six audit categories passed | [governance](governance.receipt.json) |
| Generated inventory | 124 claims, 68 Lean proofs, 376 source openings | [proof-bank](proof-bank.receipt.json) |
| Markdown integrity | 407 source files checked | [markdown](markdown.receipt.json) |
| Vendored package pins | All match | [vendor-pins](vendor-pins.receipt.json) |
| Inventory and Markdown-link tests | 61 passed | [inventory-tests](inventory-tests.receipt.json) |

The [manifest](manifest.json) binds all commands, exact source, integration
scope and source hashes. The [original full native packet](../native-packet.txt.gz)
is reproduced byte-for-byte, with SHA-256
`3d3681a85a5b4f1bc4cca5839c5fe2ac37a91ab50b9014e947b984d020a4037d`.
The local pinned runtime scope and retained Crashpad warning are unchanged.
The following archival commit changes only these evidence records and
their index. Live hosted CI is reported separately in PR #497; local
execution does not imply a hosted pass or independent human review.
