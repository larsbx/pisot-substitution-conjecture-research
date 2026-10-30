# Class-C lower strip: exact certificate packet, 2026-10-29

See [derivation and audit](../../docs/class-c-lower-strip-2026-10-29.md) and
[prior-art stop/go](../../docs/class-c-lower-strip-stopgo-2026-10-29.md).
Dependency #384 is pinned at 53dd9547cea65d3cdb1fa80c4e16f97b712aabd4;
main was 91db5726e0572be0b6c213a41ff598ce30aa0ada. No existing certificate,
engine, finite arithmetic package or governed claim status was changed.

## Quantified results

- The PIP starts are exactly n>=2d-5 (plus), n>=2d+1 (minus), for all d>=6.
  `domain.log` checks the polynomial premises; the note supplies the quadratic
  Schur/Jury proof. No claim of a complete Lean formalization is made.
- Both signs have BH on 3d+16<=n<=4d-16 (automatically d>=32), with 280/250
  constant integer labels. No label set is supplied to the engine.
- The four top layers below T_C have BH for every d>=6: plus
  4d-4<=n<=4d-1; minus 4d<=n<=4d+3. Each diagonal has its own symbolic
  certificate at d>=12 and six exact end members d=6..11.
- The whole residual strip at gap d=6 has BH (17 plus and 15 minus members).

All graph decisions are complete under a 20,000-vertex fail-closed cap.
Unknown signs, nonaffine/unbounded child intervals, non-PIP results,
non-hitting vertices, nonconstant export offsets or sample mismatches abort.
The region sign budget is k<=24; the middle certificates actually use k=0.
Finite graph sizes range up to 2,432 in this packet. These are certificates
for the canonical swap-seed graph and offset-zero target, not PDS or PSC.

## Native replay

From `kernel/`, using pinned Mojo 1.1.0.dev2026090805 (34562fa1):

```bash
mkdir -p build/class-c-lower
pixi run --locked mojo build -I . class_c_lower_strip.mojo -o build/class-c-lower/lower
build/class-c-lower/lower domain
pixi run --locked mojo run -I . tests/test_class_c_lower_strip.mojo
for eps in 1 -1; do
  build/class-c-lower/lower middle "$eps" 16 16
  build/class-c-lower/lower top-finite "$eps"
  build/class-c-lower/lower gap "$eps" 6
done
for c in -4 -3 -2 -1; do build/class-c-lower/lower diagonal 1 "$c" 12; done
for c in 0 1 2 3; do build/class-c-lower/lower diagonal -1 "$c" 12; done
```

Each output is the correspondingly named `.log`; `R` rows losslessly encode
integer labels, not edges. The dedicated workflow byte-diffs every new log.
The theorem-plus/minus replay logs and inherited native test are fresh runs
of the unchanged #384 commands, byte-diffed against its archived packet.
The theorem logs include its refused shift-0/1 cones and onset gap lines.
Those refusals are not counterexamples to BH. The adjacent 198/216 sets,
compared with frozen 196/214, disprove extension of the *same label set*.

## Independent oracle

From the repository root:

```bash
python3 oracles/python/check_class_c_lower_strip.py evidence/class-c-lower-strip-2026-10-29 > /tmp/class-c-oracle.json
diff evidence/class-c-lower-strip-2026-10-29/oracle.json /tmp/class-c-oracle.json
(cd evidence/class-c-lower-strip-2026-10-29 && sha256sum --check SHA256SUMS)
```

122 deterministic complete graph checks use literal-word prefix sweeps,
integer label transport and a separately written Fraction field/sign oracle.
All label rows agree with native receipts; native finite-member hit depths
also agree. Four middle members per sign include the corner, an interior
sample and separated parameter values. Four members per diagonal include
d=12 and d=64. All 48 finite top end members and all 32 gap-6 members are
checked, plus the two original frozen-tail samples. These finite checks do
not replace universal symbolic sign certification.

A separate exact Routh/irreducibility oracle examines all d=6..64, both signs,
and n=d-eps..4d+8: 9,558 PIP, 3,874 non-PIP, 20 refused, zero decided
mismatches with the domain lemma. All refusals lie below the domain; the
receipt lists them individually. Refused is never coerced to non-PIP.

`provenance.json` hashes the full local Mojo import closure of the drivers
and tests, both Python oracle scripts and their exact field/screen sources,
the pinned toolchain manifests and repository policy. The compiler/standard
library and the arithmetic implementation remain trust inputs. This source
review and separate implementation do not constitute independent human
review. SHA256SUMS pins every packet file except itself.

**Rebind (2026-10-30, PR #399).** Theorem T_C2 changed three pinned sources:
`kernel/psc/class_c_tail_certificate.mojo` and `kernel/class_c_tail_certificate.mojo`
(the `STRIP` frame, a several-set cover and a `strip` driver mode; `TAIL`-frame
pieces, names and outputs are unchanged) and `kernel/pixi.toml` (two tasks).
Before the re-pin, every receipt of this packet was replayed on the new
sources and found byte-identical: the native test, both middle cones, all
eight diagonals, both top-finite and gap-6 logs, the domain log, and the
three T_C replays. `provenance.json` now pins the new digests and keeps the
previous ones under `rebinds`.

**Rebind (2026-10-30, fit-first line engine).** `kernel/psc/symbolic_line.mojo`
changed only inside the line closure `_Closure`, which this packet's drivers
never call: `psc.symbolic_cone` has its own closure and imports only
unchanged helpers from `psc.symbolic_line`. Before the re-pin, all sixteen
native receipts were replayed on the new source and found byte-identical:
the native test, both middle cones, all eight diagonals, both top-finite and
gap-6 logs, and the domain log. `provenance.json` pins the new digest and
keeps the old one under `rebinds`.
