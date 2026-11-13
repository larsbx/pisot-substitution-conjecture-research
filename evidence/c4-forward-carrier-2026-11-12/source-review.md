# Independent final source review

Reviewed the current forward-carrier source read-only on 2026-11-13
UTC. No compiler, oracle replay or duplicate test suite was run for
this review. No correctness or reproducibility blocker was found.

A separate text/data comparison of both generated Lean modules against
the archived JSON verified every top and bottom word, state-array
reference, complete ordered child row, literal substitution image and
ordered seed index. Fixture 0 has 24 contiguous size-eight ranges
covering 192 rows. Fixture 1 has 65 covering 520 rows. This comparison
validates serialization only and supplies no Lean acceptance.

The fast refinement checks every listed state's irreducibility before
using `Reduction.red_unique`; a reducible whole substituted pair cannot
be accepted merely because its tracks concatenate correctly. Invalid
word decoding falls back to an empty word, which the mandatory
nonempty block check rejects even for unreachable extra states.
Explicit index-bound proofs avoid modular `Fin` numeral behavior.

The named wrapper preserves literal image order through definitional
equality. Its termination consumers retain `hp : p.Valid` and actual
seed or descendant membership. No arbitrary starting-block or general
substitution quantifier was introduced.

The amended native gate includes generated Lean sources in its source
snapshot and reproduces them byte for byte. It preserves both distinct
budget refusals, empty stdout on those refusals, independent JSON
replay and mutation tests. Provided-binary mode explicitly requires
separate build provenance and never claims it built those executables.

Remaining validation: successful concrete kernel checks, the complete
named chain and the compiled transitive-axiom audit. Source agreement
and native replay cannot replace those receipts. This is a source
review, not independent human review or an acceptance certificate.
