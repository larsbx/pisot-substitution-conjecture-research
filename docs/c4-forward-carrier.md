# Named forward carrier decision

Proceed with replay of the existing ordered reduction and closure criterion for
the two literal named substitutions. This is a specialization of the ordered
carrier argument already formalized in `Degree3Catalogue.lean`. The
[prior-art review](c4-finite-productivity-literature-2026-11-12.md) covers
Sirvent–Solomyak's finite factor graph and its edge multiplicities,
Barge–Štimac–Williams's separate coincidence condition, and Martensen's
dependence on the chosen equivalence. The present check uses exact Parikh
reduction and terminal coincidence, with the repository's length-two swap
seeds. It makes no identification with the literature's prefix-seeded BPA.

Use the existing normalized discovery engine, then replay canonical
unnormalized decomposition on both tracks in each order. Compare full rows
with Lean reduction, including ordered multiplicity and coincidences. The
carrier is the list of row sources. Omitted children, swapped tracks and
substituted images must fail; a capped discovery emits no certificate. The
finite Thue–Morse control from the prior review still prevents using finiteness
alone to claim termination with coincidence.

## Replay and scope

Run `./tools/check_forward_carriers.sh` with the pinned Lean and Mojo toolchains
and mathlib cache. The canonical builder uses a 20,000-state budget and a
40,000-letter state-length budget. The 10,000- and 20,000-letter runs for
`1/021/001` exhausted the length budget and were inconclusive. The two
completed exports gave these native observations:

| Substitution | Swap orbits | Ordered rows | Child occurrences | Longest track |
|---|---:|---:|---:|---:|
| `1/021/001` | 97 | 192 | 5,652 | 35,437 |
| `1/012/001` | 261 | 520 | 4,386 | 4,872 |

The raw generated Lean data SHA-256 values are
`4416b22f608eff9a405725146b1fe95a5ff3e108ee560cf07a85ff4e5ba8e74d`
and `c2988a9770db9cfd8698040ce85ae224174de27261def0f70d014d63cb573b63`,
respectively. Coincidence rows have no outgoing children. Noncoincident rows
retain every occurrence, including terminal children. The checker binds all
three images to the expected literal substitution, checks all six ordered
roots, and verifies ordered track concatenations and each factor's first
zero-return condition. Uniqueness then supplies equality with Lean's
`red`; `bpaStatesNC_subset` gives finiteness.

The native enumeration is complete for both fixtures. Exact-revision Lean
acceptance requires the two concrete replays and axiom reports. The seed
termination consumer retains a valid original archive packet and a matching
fixture identity. These six seeds do not cover arbitrary initial blocks.
