# Consolidated rational-root optimization (2026-10-16)

## Decision and provenance

Baseline: `main@f6e181d1d4fe4a4f02f8dbb09bbb28538ad1b8f9`.
PR #267 (`f8706120fbfcd9b4736a6bd880eacbfdee70f29a`) and PR #275
(`cc6149ee0e9d92911745935047a5f003122cffe6`) both replace rational candidate
evaluation with integer Horner and enumerate divisor pairs on demand. They
are alternatives, not additive improvements. This consolidation retains the common integer-Horner optimization and the
original ascending Python divisor traversal, with the compatibility fallback
below. Canonical Mojo streams the small divisors in ascending order and then
visits the deferred complements in reverse collection order. #267's nested
function and repeated slicing are unnecessary. #275's immediate complementary
candidates were rejected after the new review found a high-degree slowdown. Neither
original PR should be merged after this consolidation.

This is a regression/performance change to the existing reviewed contract;
no new theorem-facing diagnostic or proof claim is introduced. Existing
literature scope remains `docs/pisot-screen-literature-gate-2026-09-16.md`.

## Exactness and refusal boundary

A rational root of a monic integer polynomial is an integer dividing its
constant. Divisor enumeration covers every positive divisor: each
`d <= sqrt(abs(constant))` contributes `d` and `abs(constant)/d`, with a square
root visited once. Candidates are evaluated by ascending magnitude, testing
both signs. Constant zero returns immediately. Candidate order cannot change
the existential predicate, but greatly affects the cost of big-integer arithmetic. Integer
Horner performs exactly the same recurrence as rational Horner at an integer
argument. Trailing zero coefficients leave the value unchanged.

Python's unbounded `int` is used only for coefficients whose exact type is
`int`. Accepted subclasses (including bool) retain the original sorted-divisor
and exact-evaluator path, preserving their existing behavior rather than
invoking overloaded native arithmetic. `_divisors` is therefore still used.
Mojo uses the vendored `BigZ` addition/multiplication, not machine-integer
Horner and not a new local arithmetic implementation.

The canonical loop also avoids two machine-boundary hazards: `abs(Int.MIN)`
and `d*d` overflow. It holds the constant magnitude in UInt64 and tests
`d <= c//d`. Signed candidates are lifted to BigZ without narrowing `2^63`.
The old implementation returns false on the direct witness
`[-2^63, 2^63-1, 1]` because its signed magnitude is negative; the new regression
tests its root 1 directly, without an impractical scan to sqrt(2^63). This is an explicitly identified boundary correction, **not**
a claim of bit-for-bit equivalence to that erroneous negative. The mathematical correction is explicit; no refusal policy is relaxed.

Public validation, the degree-one exception, degree >3 refusal when no linear
factor is found, Routh singularity refusal, and unit-circle rejection are
unchanged. In particular `(x²+1)²` remains refused for irreducibility, never
promoted merely for lacking rational roots. The entire Python AST outside
`_has_rational_root` is checked identical to pinned main by the replay script.

## Deterministic correctness evidence

- `tests/test_rational_root.py`: 19,607 monic polynomials of degrees 1–5 with
  nonleading coefficients in [-3,3], also padded with zeros, against ordinary
  Fraction Horner and independent sorted-divisor enumeration. Public
  irreducibility is checked for each. Targeted examples include both root
  signs, zero constant, square divisors/repeated roots, ±1,000,003 roots,
  highly composite constants, 100-bit coefficients, the degree-5,000 small-root review counterexample, known irreducible
  examples and reducible polynomials without linear factors.
- Subclass arithmetic traps and bool coefficients retain the exact fallback.
  A work-count regression fails on main: plain-integer root checks now
  construct zero Fractions. Timing is never a correctness assertion.
- `kernel/tests/test_rational_root.mojo`: independent frozen rational baseline
  on all 729 cubics in [-4,4]^3, padding, targeted examples, intermediates
  exceeding Int64, the Int.MIN witness, a degree-128 small-root control and public refusal/negative controls.
  It declares a contract receipt, not a new theorem claim.
- Replay compares root and irreducibility verdicts against pinned main for
  the same 19,607 Python specimens. All 729 cubic `screen` results agree:
  89 pisot, 621 not-pisot, 19 refused.

## Reproducible performance evidence

Run from the repository root (Python >=3.10 and the pinned git history):

```sh
python oracles/python/rational_root_benchmark.py > /tmp/rational-root.json
cd kernel
pixi run mojo run -I . -I tests tests/test_rational_root.mojo
pixi run mojo run -I . -I tests rational_root_bench.mojo
```

Raw samples, source hashes, compiler/Python versions and machine context are
retained in `evidence/rational-root-2026-10-16-r2/`, covered by SHA256SUMS.
The initial streaming measurements in `evidence/rational-root-2026-10-16/`
are retained verbatim but superseded; they do not describe the selected implementation. Each
benchmark uses seven paired alternating batches after exact-result warm-up;
Python additionally pins CPU affinity and retains process CPU timings. The
Mojo benchmark checks each polynomial before timing and checks timed result
sums. The canonical benchmark also runs in CI and uploads its raw output.

| Workload | Python median before/after speedup | Canonical Mojo speedup |
| --- | ---: | ---: |
| 729 cubic coefficient grid | 2.60× | 37.23× |
| Many-divisor no-root examples | 3.67× | 30.46× |
| Large positive/negative complementary roots | 1.04× | 7.48× |
| Zero constant (unchanged early exit) | 0.91× | 0.92× |
| Known irreducible examples | 2.12× | not measured separately |
| Reducible without a linear factor | 2.27× | not measured separately |
| Public irreducibility on cubic grid | 2.20× | not measured separately |
| Full screen on cubic grid (unchanged control) | 0.96× | not measured separately |
| Small root, high degree (Python 5,000; Mojo 128) | 1.45× | 103.57× |

These are local shared-host observations, not universal speed guarantees.
Especially the trivial zero fast exit is timer-sensitive. Current main already
optimizes generic Python `evaluate`, so the earlier approximate sixfold claim
is not the baseline here. Much larger canonical gains reflect removal of
unbounded rational normalization, not stronger mathematics. Divisor search
remains O(sqrt(|constant|)) worst-case, with O(degree × number-of-divisors)
Horner steps and variable-cost exact arithmetic. Ascending traversal avoids expensive large candidates before small roots; it
does not make trial division suitable for arbitrary huge primes. Divisor
storage is O(number-of-divisors), an intentional tradeoff against that slowdown.

## High-degree review correction

PR #278 review identified `(x-2)(x^(n-1)-2520)`: the initial streaming pair
order tries ±5040 before discovering the root 2. Horner at those large values
creates degree-dependent huge intermediates; the reported degree-50,000
Python slowdown was not independently timed here, but its mechanism is exact.
The revised benchmark explicitly includes this family at degree 5,000 in
Python and degree 128 in Mojo. Both now visit ±1 and then 2 before any large
complement. The original streaming speed figures, including the 48.84× Python
large-root result, are withdrawn for the selected implementation, not silently
overwritten. Integer Horner alone remains a measured improvement on the grid.

## Review disposition and side notes

#267's canonical-language, regression/benchmark and subclass findings are
addressed above. #275's regression/benchmark finding is addressed by committed
replayable evidence. Both `.jules/bolt.md` entries are excluded: their 2024 dates
are unsupported, the speed claims lack reproducible provenance, and a parallel
ledger violates policy. The tooling lesson is recorded with today's date in
`docs/side-notes-ledger.md`: disposable scratch scripts should not be committed;
durable benchmark programs and their evidence deliberately must be retained.
Existing canonical ledger bytes are preserved; this session only appends.

No PSC result, theorem status, certificate coverage domain, or claim promotion
follows from these speed measurements.
