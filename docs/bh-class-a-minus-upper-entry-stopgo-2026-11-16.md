# Minus Class-A upper region: bind the literal boundary and recurrence proofs

Baseline is PR #577 at `59adf93f61ea5b7cecc78526b2099fa410c36bc0`. Proceed
with the literal family `n = k+t+3`, `d = k+2*t+5`, on `t >= 6`, which
contains the remaining complement `t >= 6, t >= k`.

The primary-source review in
[the preceding gate](bh-class-a-central-entry-stop-go-2026-11-14.md) applies.
Minervino and Thuswaldner's marked prefix-suffix setting motivates retaining
the actual occurrences. Akiyama and Lee's criterion requires a realized
tiling and is outside this finite-word proof. The floor recurrence of
Kirschenhofer et al. does not discharge the nearest-integer cycle exits.

The finite-window route in the [written proof](class-a-central-entry-2026-11-14.md)
can give a threshold `24*(n+4)` here, but formalizing that threshold is
unnecessary for entry. The exact existing `minus_class_a_strict_enters_run_gap`
theorem takes an arbitrary strict packet into the RUN interval when
`n >= 7`. The literal `enters_central_run` theorem then emits original
ordinals and a half-unit center bound. Instantiate these interfaces with a
bracketed real root and the exact normalized length equations. Check the
change of offset coordinates and retain both original index tracks.

Bind the signed scalar recurrence to true RUN occurrences, reconstruct
the full alternating packets and prove their exits from actual words.
The generic alternating classification has a genuine nonzero-cycle control.
Any escape construction must keep the legal two-track ordinals and full
integral target. Preserve the scope of the existing acceptance records and
audit the new endpoints separately.

## Lean endpoint and replay

`ClassAMinusUpperEscape.complement_to_zero` uses one bracketed root for
each member and quantifies over every strict integral source. Each witness
is an `OrderedInteriorPath` ending at `packet 2 2 0 0 0`. The two
original prefix tracks can be extracted with
`ordered_path_traced_zero_original_prefixes`.

The nearest RUN child has an exact strict error bound because a half-unit
displacement would give a quadratic with an odd linear coefficient at the
irreducible cubic root. The scalar tail reconstructs the full packet
`(H,3H,-6H)` or its track reversal. The positive coefficient
`K=2n-d` gives the integer guard `K*H <= n-2`. For `K*H >= 4` two
literal digits enter the reversed unit strip, where the two-step transfer
reduces the height. The remaining five positive factorizations have
explicit routes of at most five digits. The `n>=9` hypothesis ensures the
written small-case LAST exception at `n=6` cannot occur here.

From `proof/PscVerif`, using its pinned Lean and Mathlib:

```sh
lake build +PscVerif.ClassAMinusUpperEscape
lake env lean -DautoImplicit=false ClassAMinusUpperEscapeAudit.lean
```

The type audit also rejects touching unit intervals as source packets. The
axiom audit checks entry, cubic irreducibility, half-unit exclusion,
alternating reconstruction and both zero-hitting endpoints.
