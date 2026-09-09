# PscVerif — Lean 4 proofs for the PSC Spectral module

Machine-checked proofs of the finite algebra of `PROOF_CERTIFICATE.md` §§3–9.
See `../docs/verification-architecture.md` for how this layer relates to the
Mojo kernel and the TLA+ specs, and `PscVerif/Spectral.lean` for the precise
list of what is and is not proved here, next to the axiom audit.

```bash
lake exe cache get   # fetch the prebuilt Mathlib
lake build PscVerif
```

The build must finish with no warnings, and every `#print axioms` line in
`PscVerif/Spectral.lean` must report only `propext`, `Classical.choice` and
`Quot.sound`. A `sorryAx` anywhere would mean a gap.
