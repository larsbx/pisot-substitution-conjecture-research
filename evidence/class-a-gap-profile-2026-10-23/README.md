# Class-A residue profiles, d = 1..16 — 2026-10-23

Exploratory finite observation for `docs/class-a-gap-uniformity-stopgo-2026-10-23.md`.
It is not a certificate and claims nothing uniform in `l` or `d`.

- `profiles/profile-dD-epsE.log` / `.exit`: `kernel/class_a_residue_ray.mojo profile D E 64`
  for `D = 1..16`, `E = +-1`. Every member `n <= 64` of the line's domain
  is built as an exact complete graph under the 20,000-state cap and must
  hit (`SUMMARY n vertices max_depth recurrent`; a non-hitting vertex or
  an exhausted cap aborts). Then, per residue `r`, the vertex count is
  fitted as `slope l + constant` from the two largest members with `l>=2`
  (`PROFILE ... affine 1|0`).
- `profile-tests.log` / `.exit`: `kernel/tests/test_class_a_gap_profile.mojo`,
  the profile equal to the proved carrier cardinality on all 18 tabulated
  rays (`d<=4`).
- `mojo-version.txt`: the lock-matched compiler used. This is not a CI receipt.

Flags (`affine 0`) and slopes other than 40 at `d>=14` reflect members
below the l-threshold within `n<=64` (see the note); they are not breaks.

```sh
(cd kernel && pixi run --locked mojo run -I . class_a_residue_ray.mojo profile 12 1 64)
(cd kernel && pixi run --locked mojo run -I . tests/test_class_a_gap_profile.mojo)
(cd evidence/class-a-gap-profile-2026-10-23 && sha256sum -c SHA256SUMS)
```

`SHA256SUMS` covers every file in this packet except itself.
