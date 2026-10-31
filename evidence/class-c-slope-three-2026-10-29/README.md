# Class-C slope-three cover — 2026-10-29

[Derivation, cover and remaining strip](../../docs/class-c-slope-three-2026-10-29.md).
[Stop/go and explicit experiment budget](../../docs/class-c-slope-three-stopgo-2026-10-29.md).

## Scope

For every d>=6, canonical swap-seed BH holds on plus n>=3d+4 and minus
n>=3d+6. The quantified graph statements use the unchanged trusted symbolic
cone engine. Local certificates are complete; hosted validation and independent
human review remain separate debts. No spectral or full PSC claim is made.

The cover combines:

- plus cone 3d+4<=n<=4d-16 (280 labels);
- minus cone 3d+8<=n<=4d-16 (250 labels);
- minus lines n=3d+6 and n=3d+7, d>=24 (250 labels each);
- 26 upper bridging diagonals, d>=24;
- 189 plus and 225 minus exact end members, d=6..23;
- #390's four top layers and #384's tail, at unchanged source hashes.

plan.json specifies the final cover, the stronger finite-end intercepts,
the middle intercepts and the two extra lower lines explicitly. The
unbounded cover proof is in the note. coverage-*.log is a separate finite
partition audit, not a proof by enumeration beyond d=64.

## Replay

From kernel/ with the repository's pinned compiler:

```bash
mkdir -p build/class-c-slope-three
pixi run --locked mojo build -I . class_c_lower_strip.mojo -o build/class-c-slope-three/lower
pixi run --locked mojo build -I . class_c_slope_three.mojo -o build/class-c-slope-three/cst
build/class-c-slope-three/lower middle 1 4 16
build/class-c-slope-three/lower middle -1 8 16
for c in $(seq -15 -5); do build/class-c-slope-three/lower diagonal 1 "$c" 24; done
for c in $(seq -15 -1); do build/class-c-slope-three/lower diagonal -1 "$c" 24; done
for c in 6 7; do build/class-c-slope-three/cst lower-line -1 "$c"; done
build/class-c-slope-three/cst finite 1 4
build/class-c-slope-three/cst finite -1 6
build/class-c-slope-three/cst coverage 1 4
build/class-c-slope-three/cst coverage -1 6
build/class-c-slope-three/cst controls
pixi run --locked mojo run -I . tests/test_class_c_slope_three.mojo
```

The dedicated workflow byte-diffs the successful outputs. For finite output,
`gzip -dc finite-plus.log.gz` or its minus counterpart recovers the complete
native stdout losslessly. Compression uses zero timestamp. finite-members.csv
is the readable complete inventory of those 414 members, sizes and depths.
Every native graph uses the inherited 20,000-vertex fail-closed cap. No graph
or path is inferred from a capped/refused result. The region sign budget
is Pólya exponent <=24; both successful cones use exponent 0.

From repository root:

```bash
python3 oracles/python/check_class_c_slope_three.py evidence/class-c-slope-three-2026-10-29 > /tmp/class-c-slope-three-oracle.json
diff evidence/class-c-slope-three-2026-10-29/oracle.json /tmp/class-c-slope-three-oracle.json
(cd evidence/class-c-slope-three-2026-10-29 && sha256sum --check SHA256SUMS)
```

The oracle passes 547 complete graph checks and ten exact sign controls.
It uses the independently written literal-word/Fraction implementation
from #390. It checks full label sets and all-vertex hitting, with exact
finite-member depths; each symbolic family is checked at four members,
including its corner. These are finite cross-checks, not substitutes for
universal symbolic signs. The archived oracle receipt includes all members,
row/graph hashes and negative controls. Tarski sign controls are also checked
by rational interval arithmetic and are bound to the *actual* refused native
polynomials by parsing their serialized coefficient arrays.

## Preserved unsuccessful proposals

The eight corner proposals were exactly plus (4,10),(8,10),(4,16),(8,16),
minus (6,4),(8,4),(6,16),(8,16). Five refused; all raw refusal logs remain.
A second successful plus (8,16) cone is retained, although the stronger
(4,16) cone is used in the final cover. No proposal was selected by counts.
The fifth refusal motivated the two separate minus lower lines, rather
than silently extending the (8,16) inequality.

The ten native sign reads certify opposite signs on each refused region;
the full coefficients and exact integer members are printed. A varying
intermediate clipping sign blocks that unsplit sign path. It does not
refute BH. The endpoint graphs have 280/250 labels respectively.

Equal counts are also inadequate: plus c=-8 and c=-9 have 282 labels but
different sets. Minus d=40,n=125 has 252 rather than 250 labels. Neither
negative control is described as a non-hitting member.

## Provenance and trust

Initial main: 625154ed470df4eef89577e421026f0c808287fd. Dependency #390 head:
8a25fe39ff78dab2d148fee23d894a988e5cea1d, merged as baf2eab4. Its 67 pinned
certificate/oracle/toolchain source hashes match the current checkout.
Its hosted jobs were still queued at the initial inspection; merge status
is not counted as a successful hosted receipt.

provenance.json hashes the full local import closure of both native drivers
and the regression test, the Python oracle and its field/screen sources,
toolchain manifests and repository policy. Compiler: Mojo
1.1.0.dev2026090805 (34562fa1). SHA256SUMS pins every packet file except itself.
The compiler, arithmetic implementation, sign engine and closure implementation
remain trust inputs. No old evidence, vendored package or governed claim status
is changed. The handwritten coverage argument is inspectable, not Lean-checked.
