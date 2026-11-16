# Fresh upper recurrence and cycle-completion acceptance

Attempt 1 completed successfully with exit 0. The process took
1,012.433 seconds and did not exhaust its 2,100-second cap. It used an
empty workspace temporary directory, fresh pinned dependency checkouts,
25 selected upstream roots and 2,165 upstream artifacts. All 22 local
library modules and both standalone audits were compiled from source.
No local project `.olean` was reused.

`source-bindings.json` pins all 132 source/configuration files. Its SHA-256
is `8fd66b738fe7bc3ca4b2235ffa38585fcbfa3c05fc1ee27f417d27a400763872`.
Both source trees and dependency pins were rechecked after cloning,
upstream retrieval, compilation and both audits. The outer process also
binds the gate, parser, generator, generated inventories and parser tests
before and after execution.

`attempt-1.log` is the unchanged producing output, SHA-256
`07e08678622a6e74d145721204ab5e6b23d3484fa3a1e7b0a67173f5f9343ac5`.
`audit.log` is its exact contiguous pair of audit transcripts, not a
synthetic fixture or a later compilation. The strict receipt parser
accepted both complete records, and the final source recheck and terminal
gate completion marker followed them.

| Module | Owned declarations | Theorem declarations | Exact endpoint types | Rejection controls |
| --- | ---: | ---: | ---: | ---: |
| `ClassAPlusUpperRecurrence` | 96 | 80 | 13 | 39 |
| `ClassAPlusUpperCycleCompletion` | 20 | 18 | 4 | 12 |
| Total | 116 | 98 | 17 | 51 |

Each audit independently restates its expected theorem types, checks
compiled ownership and all owned declarations' transitive axioms, and
rejects missing, wrong-typed and extra-premise substitutes. Only
`propext`, `Classical.choice` and `Quot.sound` are permitted. The raw build
log retains ordinary Lean linter warnings.

The exact formal scope is in `receipt.json` and the
[written theorem's formal-coverage section](../../../docs/class-a-plus-upper-central-recurrence-2026-11-15.md#formal-coverage-and-the-remaining-assembly-boundary).
The scalar recurrence, literal RUN interfaces and complete signed cycle
exits are verified. Root existence/no-half-tie selection, construction of
the actual infinite central trajectory and full end-to-end formal
assembly remain separate. Arbitrary strict-source entry is not proved.

Development attempts are preserved in `../lean-development/`. Their
successes are not substituted for this fresh producing process. No hosted
or future integrated revision is accepted by this local receipt.
