# Return-word derivation probe — 2026-10-11

Exploratory script behind `docs/sadic-transfer-literature-gate-2026-10-11.md`
§4 and the side-notes ledger entry of 2026-10-11. **Provenance, not canonical
code** (AGENTS.md); nothing in a proof rests on it.

| file | what it is |
| --- | --- |
| `return_word_barge_probe.py` | enumerates Theorem K's family `sigma(o) = y`, `sigma(y) = o w1 o`, `sigma(z) = o w2 o` with `|w1|, |w2| <= 4`; keeps primitive members (exact) with `|det M| = 2` (exact) and a Pisot spectrum (**float** screen, tolerance `1e-9`); derives each at every letter on return words (Durand; power `k <= 9`, 3,000-letter fixed-point prefix, a missing return word raises rather than concluding) and tests the derived substitution and its square for Barge's class or its mirror |
| `return_word_barge_probe.out` | its output, one line per member: 130 members, 0 with a derived witness; `z` is never derivable (`sigma^k(z)` begins with `o` or `y`) |

Budget: the word-length cap, `k <= 9`, the prefix length and derived powers
1–2. A member outside the cap, or a witness at a higher power, is not ruled
out. Run with `python3 return_word_barge_probe.py` (needs numpy).
