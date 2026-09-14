# substitution_dynamics

Finite words, substitutions, balanced pairs, the balanced-pair automaton, and
swap-walk discrepancy over an explicit alphabet `{0, ..., size-1}`.

Extracted from the PSC research kernel (`psc/words.mojo`, `psc/bpa.mojo`,
`psc/swap_discrepancy.mojo`) as step 3 of
`docs/library-extraction-candidates-2026-09-14.md`. The package is the
computational subject only: it carries no Pisot vocabulary (no G1, C3, C4,
producer, or renewal), no fixed alphabet, and no theorem claims.

| Module | Contents |
| --- | --- |
| `substitution.mojo` | `Substitution` (validated images, `apply`, `apply_n`, prefix/suffix endpoint maps, image prefix lengths, incidence), `validate_word` |
| `words.mojo` | `parikh`, streaming `n2`/`n3`, `idx3`, `Pair`, `checked_pair`, `is_balanced`, `k1`/`k2`/`k3`, `is_zero` |
| `balanced_pairs.mojo` | `coincidence_boundaries`, `decompose`, `normalise`, `inflate_pair`, `children`, `seed_states`, boundary lineage and endpoint synchronization |
| `automaton.mojo` | `Automaton`, breadth-first `build` with a state cap, iterative Tarjan `sccs`, recurrent non-coincident components, `nonproductive_states` |
| `discrepancy.mojo` | `discrepancy`, `swap_walk_sup`, `swap_walk_profile`, `max_reachable_discrepancy`, `max_state_length`, `common_tile_count` |

## Boundary

- **Validation happens once.** `Substitution.checked(images)`, `checked_pair`,
  and `validate_word` raise a typed `Error` on a letter outside the alphabet,
  an erasing image, or an empty alphabet. Below that boundary the kernels index
  without checks; the plain `Substitution(images, size)` constructor is the
  documented trusted path for callers that validated upstream.
- **Cap means inconclusive.** `build` returns `capped = True` when it stops at
  `max_states`. A capped automaton is never a counterexample or a proof.
- **Invariant violations abort.** `inherited_boundary_positions` aborts if
  balanced prefixes ever have different image lengths; that is an impossible
  state, not a negative answer.
- **Alphabet size is explicit.** `Pair` carries no alphabet; balance and the
  invariants `K1`, `K2`, `K3` take `size` because their dimensions are `size`,
  `size^2`, `size^3`. For `size == 3` the `K3` lex index equals `psc.tensor3.idx3`.

## What stays in PSC

`psc/words.mojo`, `psc/bpa.mojo`, and `psc/swap_discrepancy.mojo` are thin
alphabet-3 views of this package with their previous names, so the census
drivers and the C4 structural modules (`derived_system`, `legal_tower`,
`hierarchy_offset`, `affine_ancestry_trace`, `endpoint_core`, and the rest)
are unchanged consumers. Those modules keep conjecture-specific vocabulary and
alphabet-3 assumptions and are not part of the package.

## Verification

`tests/test_substitution_dynamics.mojo` pins two- and four-letter automaton
counts that `tests/test_substitution_dynamics_oracle.py` derives independently
from the Python oracle `src/psc_research/bpa.py`; the tribonacci case is
pinned by both and by the alphabet-3 kernel tests. Every alphabet-3 census
assertion in CI is unchanged.
