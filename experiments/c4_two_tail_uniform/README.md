# Uniform five-generation word certificates: tails 102 and 120

For every a,b>=0 with a+b>=1, both substitutions

```
0 -> 01, 1 -> 1^a 2 1^b, 2 -> 102
0 -> 01, 1 -> 1^a 2 1^b, 2 -> 120
```

have pairwise strong coincidence by generation five. Every nonempty balanced
root has a literal diagonal in its complete fifth inflation. The uniform
source-pair bound five is sharp. These statements are proved by explicit
block-word identities in `docs/two-tail-uniform.md`, including every zero-run
boundary. Tests alone are not the proof of the unbounded quantifiers.

The executable verifier uses integer-only compressed substitution words and
checks actual prefix masses and following letters. It accepts 512-bit run
parameters without expanding huge images. No geometric, numerical spectral,
strong-coincidence lookup-table or arbitrary finite-component premise is used.
The explanatory source has no dependency on previous conversation artifacts.

## Reproduce

```
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 python -m pytest -q tests/test_two_tail_uniform.py
python oracles/two_tail_uniform.py --receipt
python oracles/two_tail_uniform.py --a 0 --b 1000000000000000000000000000000000000000000000000000000000007 --tail 102
python tools/independent_replay.py
python tools/run_validation.py
```

The verifier uses Python's standard library. Pytest runs the tests. The
separate independent replay additionally uses SymPy for eight symbolic
polynomial checks; it imports no producer code and uses a different recursive
matrix-power method for compressed prefixes.

`evidence/receipt.json` contains 24 examples, including both boundaries and
100-digit parameters, with the exhibited and propagated fifth-level positive
witnesses. It is regenerated, not trusted input to production acceptance.
`evidence/local-validation.json` gives actual commands, exit codes and source
hashes. The failed first symbolic-check harness attempt and successful repair
are retained distinctly. No native Mojo, Lean, hosted, repository-wide, or
human-referee acceptance is claimed.

The repository was inspected at main `ba09fdbd770248905a297303b8de45b3d7c5018d`.
This bundle does not mutate main, active research PRs, or claim governance.
The finite fifth-level bound is new coverage relative to the previously
recorded 012/021 and reversed 210 run-family notes; no exhaustive novelty
claim is made. It is NOT a universal result for arbitrary Pisot substitutions,
all permutations of 012, BPA termination, pure discrete spectrum, or PSC.
