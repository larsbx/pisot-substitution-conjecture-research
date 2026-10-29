# Class C below slope three — exact packet, 2026-10-29

[Derivation and coverage](../../docs/class-c-below-three-2026-10-29.md).
[Stop/go and recorded refinements](../../docs/class-c-below-three-stopgo-2026-10-29.md).

## Quantified result and scope

For every integer d>=6, canonical swap-seed BH holds on:

- plus 2n>=5d+8;
- minus 2n>=5d+16.

The new selected sectors are plus (A,B)=(8,16), with 400 labels, and minus
(16,8), with 384 labels. Here 2n>=5d+A and n<=3d-B. Both certify with
Pólya exponent zero, through the unchanged trusted cone engine. This is a
boundary-hitting result, not PDS, G1, full legal-overlap realization or PSC.
Independent human review and hosted acceptance remain separate debts.

The cover joins these sectors to #392's upper bounds with the recorded
n=3d+c lines and exact small-gap ends. The universal integer inverse and
coverage proof are in the note; coverage-*.log is a finite error detector,
not the universal proof.

## Packet inventory

- plan.json: selected sectors and all 40 separately certified line pieces,
  their replay arguments, symbolic floors and exact prefixes.
- sector-*.log: all eight proposals, four certified and four refused.
- line-*.log: all initial floor-32 proposals, 36 certified and four refused.
- target-line-*.log: six exact intersection-floor attempts, three certified
  and three refused. These retain stronger/restricted proposals explicitly.
- shifted-line-minus-*.log: the four remaining minus lines certify at d>=48.
- exceptions-minus-*.log: every required earlier member of those lines,
  52 graphs in total; no common label set across tail and prefix is assumed.
- finite-plus/minus.log.gz: complete native end records for d=6..31,
  234 plus and 286 minus graphs (520 total), using finite A=8 on both signs.
  The minus global A=16 requires a subset of this stronger finite result.
- finite-members.csv and line-inventory.csv: readable exact inventories.
- control-*.log: six complete native graphs demonstrating label changes.
- experimental-profile.json: finite independent-oracle prototype used only
  to propose regions; it is not a uniform certificate.
- oracle.json: 746 independent complete graph comparisons, all passing.
- native-test.log: exact inverse, ceiling, target-line and refusal contracts.
- provenance.json and SHA256SUMS: exact source, dependency and packet pins.

Every native graph uses the inherited 20,000-vertex fail-closed cap. Unknown
signs or fits, non-PIP members, non-hitting vertices, growing child ranges,
nonconstant export offsets and sample mismatches refuse. The sign budget is
Pólya exponent <=24; sampled agreement never supplies an undecided sign.

## Native replay

From kernel/, with pinned Mojo 1.1.0.dev2026090805 (34562fa1):

```bash
mkdir -p build/class-c-below-three
pixi run --locked mojo build -I . class_c_below_three.mojo -o build/class-c-below-three/cbt
build/class-c-below-three/cbt sector 1 8 16
build/class-c-below-three/cbt sector -1 16 8
for c in $(seq -15 3); do build/class-c-below-three/cbt line 1 "$c"; done
for c in $(seq -11 5); do build/class-c-below-three/cbt line -1 "$c"; done
for c in -15 -14 -13 -12; do build/class-c-below-three/cbt shifted-line -1 "$c" 48; done
build/class-c-below-three/cbt exceptions -1 -15 38 47
build/class-c-below-three/cbt exceptions -1 -14 36 47
build/class-c-below-three/cbt exceptions -1 -13 34 47
build/class-c-below-three/cbt exceptions -1 -12 32 47
build/class-c-below-three/cbt finite 1 8
build/class-c-below-three/cbt finite -1 8
build/class-c-below-three/cbt coverage 1 8 16
build/class-c-below-three/cbt coverage -1 16 8
build/class-c-below-three/cbt control 1 8
build/class-c-below-three/cbt control 1 16
build/class-c-below-three/cbt control -1 8
pixi run --locked mojo run -I . tests/test_class_c_below_three.mojo
```

The dedicated workflow replays the exact plan and byte-compares every selected
output. `gzip -dc finite-plus.log.gz` (or minus) recovers native stdout
losslessly; the gzip timestamps are zero. Optional proposal replays use
`sector EPS A B`, `line EPS C` or `target-line EPS C A` with the parameters
encoded in each archived filename. A native refusal remains a refusal.

From repository root:

```bash
python3 oracles/python/check_class_c_below_three.py evidence/class-c-below-three-2026-10-29 > /tmp/class-c-below-three-oracle.json
diff evidence/class-c-below-three-2026-10-29/oracle.json /tmp/class-c-below-three-oracle.json
(cd evidence/class-c-below-three-2026-10-29 && sha256sum --check SHA256SUMS)
```

The independent literal-word/Fraction oracle checks four members per selected
sector, four per symbolic line (including its actual floor), every finite end
and exceptional member, and six label controls. It compares full native label
sets and finite-member hitting depths. These finite comparisons do not
replace the uniform symbolic certificates.

The experimental profile can be regenerated with the independent `run`
function in oracles/python/class_c_lower_strip.py at d=24,40,60 and
n=floor(5d/2)+j for j=0,4,8,12 or n=3d+c for c=-16,-8,-4,0,3,5,
deduplicating each member. The canonical `member EPS D N` command is available
for every such member. Those profile rows are separate from the 746 native
comparisons and support only the stated finite observations.

## Exact controls and remaining region

The plus B=8 cones contain complete 478-label and 400-label graphs, so a
single constant label set on either whole proposed cone is impossible.
Both controls have BH; they do not refute BH on the cone. The minus control
changes from 384 labels at (40,112) to 400 at (40,116); the second member
is outside B=8, so it refutes extrapolation above that cut, not the certified
minus sector.

Some initial minus line failures occurred below their target intersection;
others required a symbolic-tail/finite-prefix split. All original failed
outputs and every exceptional integer are retained. No failed stronger
variant is quietly removed or converted into a non-BH result.

Together with the complete gap-6 result, remaining members lie in the
conservative envelope d>=7, plus 2d-5<=n with 2n<=5d+7, or minus
2d+1<=n with 2n<=5d+15. Extra line and finite certificates settle some
members inside that envelope; it is not an assertion that all are untreated.

## Provenance and trust

Dependency #392 head is 82dc6955faf68df5ee31292b9c2dd503b325a123; it was
still open with queued hosted jobs at initial inspection. Main then was
625154ed470df4eef89577e421026f0c808287fd. Its 67 recorded source hashes
match the current checkout. Local certificates are used at exactly their
recorded scope; a queued job is never called a pass.

The compiler, exact arithmetic, symbolic sign and graph implementations
remain trust inputs. Full local import-closure hashes and Python oracle
sources are recorded. No old evidence, vendored code or governed claim status
is modified. Neither the handwritten coverage argument nor this independent
finite replay is described as a complete Lean proof or human review.
