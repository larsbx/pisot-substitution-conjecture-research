# Upper plus-Class-A entry: fresh executable replay

Date: November 23, 2026. **All six replay/check commands completed successfully.**

The executable sources and existing tests are unchanged from accepted source
`1bdaa34c63e6de97a0f17998c4f06887a18f099c`, whose tree `225e933c2ca2d8aaa8be550c003e824ac93fa201` is exactly
the tree merged as `main@7bfcd8c15e845f148b3c0ee405ca839ae6039e2d`. New Lean
files have a separate build and theorem audit; these finite checks do not stand
in for that audit. No repository modifications were published.

## Results

| Check | Fresh result |
| --- | --- |
| Canonical Mojo entry test | 33,324 strict sources; 41,232 literal entry edges; exit 0 |
| Independent exact oracle | 33,684 sources; 47,412 entry edges; maximum depth 37; 96 negative controls |
| Independent comparison with native indices and full targets | All 33,324 native paths matched |
| Standalone original-prefix transcript replay | All 33,684 records and 47,412 edges accepted |
| Existing cycle, symbolic, central and independent regressions | 148 passed; no failures, errors or skips |
| Full target mutations | All 72 rejected, covering each of 3 coordinates in all 24 control members |
| Supplied original-prefix mutations | All 6 rejected, covering both full 3-coordinate tracks |
| Orientation reversal | Every one of 33,684 records preserves depth, swaps every index pair, negates each complete target and exchanges both prefix tracks |
| One-edge y/c counter-control | All 9,192 possible one-edge children across the 24 members fail to be central |

The exact grid uses `n in {7,8,12,31}`, `J in {1,2,3,4,5,n+7}`, all nine
ordered types and the documented integral-coordinate window. The independent
oracle additionally includes the documented near-boundary powers. Its step cap
is 128, exact root-refinement cap is 512, and inherited literal-word cap is
50,000; exhaustion refuses a verdict. All five selector branches were exercised:
32,508 direct, 10,530 growth, 666 LAST/first-RUN, 3,070 reverse LAST/FIRST,
and 638 last-RUN/FIRST edges.

Both documented output hashes were reproduced exactly:

- Native stdout: `36ef371410b3817ddcde53403c25d972c4a9b4e035e7a7f3a93bb2d5e83d5acb`.
- Full JSONL: `c1dccf0c6f7f1ae8fcc953733035d705741e14787f5cf56c9890a3617015688d`.

## Required two-edge control

For each tested member, the literal y/c source with bottom-minus-top offset
`(0,1,0)` follows exactly `(n+2,0)` then `(1,2)`, with intermediate full offset
`(0,1,-1)` and terminal y/y offset `(0,0,0)`. The wrong top index `n+1`, an
altered intermediate coordinate, a truncated path and a literal touching child
are refused by the documented controls.

For the concrete member `n=7, J=1, d=25`, the indices are `(9,0),(1,2)` and
the complete original prefix vectors are `P=(10,9,96)` and `Q=(0,1,1)`.
The reversed source has indices `(0,9),(2,1)` and exchanges P and Q. Reversal
adds no substitution edge.

## Scope and review

These computations establish the declared finite calibration and transcript
integrity. The independent oracle also freshly composes 22,748 sampled entries
with the existing central constructor to typed zero. This does not close the
remaining general central-source Lean theorem. Universal BH, residual A1′ and
general C4 receive no promotion. The existing regression files include replay
of archived native cycle/central receipts; this session freshly generated the
native **entry** receipt.

Source review of the new literal-entry and bound modules found no mathematical
blocker: the stored Packet offset has the opposite sign from the prose, and
the bridge explicitly uses `shift=-offset`; each boundary child has the actual
FIRST/RUN/LAST marks; the first RUN/RUN packet discharges no-half ties on its full
integral vector; growth retains the orientation frame even at zero shift; and
the endpoint retains a possibly nonzero central full offset. This is source
review and mechanical evidence, not independent human validation.

The older Nov 16 non-claim about small parameters is superseded at canonical
swap-seed scope by the 70-member Nov 20 certificate note. Nothing here upgrades
those finite certificates to all-strict-source coverage.

## Runtime and replay commands

Python 3.12.14; pixi 0.84.2; Mojo 1.1.0.dev2026090805 (34562fa1); pytest 9.2.0.
Use fresh output paths when repeating the commands: transcript creation and
the extra-controls script refuse to overwrite existing outputs.

Working directory: `/workspace/scratch/c388c36ccd77/psc-upper-entry/kernel`

```sh
MODULAR_TELEMETRY_ENABLED=0 MODULAR_CRASH_REPORTING_ENABLED=0 /workspace/scratch/402f1bb377be/psc-ray-runtime/pixi/pixi run --locked mojo run -I . tests/test_class_a_plus_upper_entry.mojo --emit
```

Working directory: `/workspace/scratch/c388c36ccd77/psc-upper-entry`

```sh
python3 oracles/python/class_a_plus_upper_entry_independent.py --transcripts /workspace/scratch/c388c36ccd77/checks/upper-entry.jsonl
```

Working directory: `/workspace/scratch/c388c36ccd77/psc-upper-entry`

```sh
python3 oracles/python/class_a_plus_upper_entry_independent.py --replay-transcripts /workspace/scratch/c388c36ccd77/checks/upper-entry.jsonl
```

Working directory: `/workspace/scratch/c388c36ccd77/psc-upper-entry`

```sh
python3 oracles/python/class_a_plus_upper_entry_independent.py --native /workspace/scratch/c388c36ccd77/checks/upper-entry-native.txt
```

Working directory: `/workspace/scratch/c388c36ccd77/psc-upper-entry`

```sh
PYTHONPATH=/workspace/scratch/402f1bb377be/psc-ray-runtime/python-checks python3 -m pytest tests/test_class_a_plus_upper_cycles.py tests/test_class_a_plus_upper_symbolic.py tests/test_class_a_plus_upper_recurrence.py tests/test_class_a_plus_upper_recurrence_independent.py -q --junitxml=/workspace/scratch/c388c36ccd77/checks/upper-regression.xml
```

Working directory: `/workspace/scratch/c388c36ccd77/psc-upper-entry`

```sh
python3 /workspace/scratch/c388c36ccd77/checks/verify-entry-extra-controls.py --root /workspace/scratch/c388c36ccd77/psc-upper-entry --transcript /workspace/scratch/c388c36ccd77/checks/upper-entry.jsonl --output /workspace/scratch/c388c36ccd77/checks/upper-entry-extra-controls.json
```

The pixi optional GUI-package post-link warning and the AnyIO pytest-plugin
deprecation warning were nonblocking; both appear in the retained logs.

## Artifact hashes

`replay-summary.json` contains exact source hashes as well as these outputs.

| Artifact | SHA-256 |
| --- | --- |
| `upper-entry-native.txt` | `36ef371410b3817ddcde53403c25d972c4a9b4e035e7a7f3a93bb2d5e83d5acb` |
| `upper-entry-native.err` | `2ae6373f021730d7d70807704313e2c7c8bc65926b7cfc266fa7e115c3987444` |
| `upper-entry.jsonl` | `c1dccf0c6f7f1ae8fcc953733035d705741e14787f5cf56c9890a3617015688d` |
| `upper-entry-oracle.log` | `5b1325f8a534961c9e564ecc4c1e662ba32310e9d484179fbd4d97c7d7f8c581` |
| `upper-entry-standalone-replay.log` | `35227f2e1af9f7b604986c9091dff1047cbf93f15c8c14de02ad3306737e0551` |
| `upper-entry-native-comparison.log` | `75ed855299d975924ea2d59654e74b87f4c559ab3bd66f839cda6e9b40accff7` |
| `upper-entry-extra-controls.json` | `4f470bdecf96fa7ec5a508f4263cb3a774f497f5f2e0f1445ecd4a5ff490273b` |
| `upper-entry-extra-controls.log` | `4fc7f0b7dea4a711d16b587050f5deae895d2f2ebd9a77f6acc3f63a11294819` |
| `upper-entry-two-edge-example.json` | `bcffa1530ff6d4ca6daf56c352ede99afff8ec9e853ab0d4cac102aed5715661` |
| `upper-regression.log` | `85bec7cd6c16e7c39eb5afcd5862b1eaf8300e6fc29869ceadd7733321d81541` |
| `upper-regression.xml` | `4c009524d65e1219b56606054feee5aae9ab89ad0e42a19f82457976e3cb8a5f` |
| `verify-entry-extra-controls.py` | `fb9251880ba2ec432989b53d269d0e53053803f174b24efea359f3ee960cb28f` |
