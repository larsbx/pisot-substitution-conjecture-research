# Class C residual-domain exact replay (2026-10-29)

Independent evidence for
[the exact PIP-domain theorem and residual BH audit](../../docs/class-c-residual-domain-2026-10-29.md).

## Standalone finite oracle

```sh
python3 evidence/class-c-residual-domain-2026-10-29/exact_oracle.py --verify
```

The script uses only Python's standard library (`fractions.Fraction`, integer
triples, graph search and SHA256). It does **not** import Mojo, NumPy,
SymPy, a floating-point root finder or the symbolic cone engine.
It enumerates all pairs of letter occurrences when constructing children,
not the native kernel's optimized sliding-window algorithm. Exact signs of
algebraic numbers are decided using rational isolating intervals; the
isolating premise is justified by Theorem P_C. Offsets are reconstructed
from the three exact tile lengths and must have integer Parikh coordinates.
The graph cap of 20,000 is fail-closed.

The independent finite controls reproduced the following constant complete
typed-row digests at three separate gaps `d=6,7,8`
(the SHA256 of the concatenated `R ...\n` lines, **not** of the GitHub
profile file including its header):

| eps | n - 4d | vertices | typed rows | SHA256 |
| --- | ---: | ---: | ---: | --- |
| +1 | -2 | 204 | 85 | `10c245fe80787d678dfd7be845444218e8bb46a4447f1af6b55faf067485456b` |
| +1 | -1 | 198 | 79 | `ebd171051da78cb1a1b6f95575dce2f853f9360691753250a178fc7e2ab459db` |
| +1 | 0 | 196 | 77 | `9683f1246f8544040e994fe0fee40032c32a3178030e84f400a28eee6b308e9d` |
| -1 | 2 | 222 | 89 | `82c463df520d7c44d68e5aa13595c57a784b6a2d2ee4441822ff451e2c6be929` |
| -1 | 3 | 216 | 83 | `c56befeabe9e60f1ff177f8d5c0c173b0b34e540b380bf8245fe2e27c117d439` |
| -1 | 4 | 214 | 81 | `3db95e539e8d444311c5b5e81e0eaa9ca3e7114078d2799dfbb35f9af241797b` |

On the plus lower PIP boundary `(d,n)=(6,7)`, the same oracle returned
2,432 vertices and zero nonhitting vertices. On the minus lower PIP
boundary `(6,13)`, it returned 1,283 vertices and zero nonhitting vertices.
Those two finite graphs are **not** claims for every d.

All six three-gap checks compare **complete normalized typed-row contents**,
not only counts or hashes. Digest values above pin the output format. The
original finite tail counts, frozen-tail row prefixes and separate negative
controls match the packet in merged PR #384. These independent calculations
are not a second proof of the quantified symbolic cone theorem.

## Native certificate and trust boundaries

```sh
cd kernel
pixi run --locked mojo run -I . class_c_pip_domain_check.mojo
pixi run --locked mojo run -I . class_c_residual_diagonals.mojo 1
pixi run --locked mojo run -I . class_c_residual_diagonals.mojo -1
```

The PIP-domain theorem has a separate hand proof and does not depend on
these finite runs. The two `class_c_residual_diagonals` attempts reuse the
trusted symbolic cone engine for `d>=8` and the native exact kernel for
`d=6,7`; acceptance requires successful hosted replay. The
`class_c_residual_probe` is an optional BH-only sign/closure tester for
further diagonals, gap lines and cones, not a uniform result by itself.

Provenance: merged PR #384 at `53dd9547cea65d3cdb1fa80c4e16f97b712aabd4`,
merge `40823631b1ed456509440263de9b100e596b314e`. Independent
finite oracle was run locally on Python 3; Mojo was not installed there.
CI workflow `.github/workflows/class-c-residual-domain.yml` performs
the native replays and uploads exact receipts. Do not promote a BH
claim from an unrun or failed native job.
