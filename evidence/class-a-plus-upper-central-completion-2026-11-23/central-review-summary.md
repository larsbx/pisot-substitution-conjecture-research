# Upper plus-Class-A central completion: independent review and replay

Date: November 23, 2026. Base is the **local entry checkpoint** `5b8bd353f1934e67b8fbac518a9737eb7abf127d`, tree
`864056322209048593cf1d0946cf9bfcea1e65b2`. All canonical executable/oracle sources and existing tests remain
unchanged from that checkpoint. No repository changes were published.

## Fresh acceptance

| Check | Result |
| --- | --- |
| Canonical native central constructor | 818 sources, 4,728 literal edges, 1,806 nearest edges; 28 native refusal controls |
| Independent source-bound oracle | Same 818 sources and counts; 15 rejected transcript mutations and 3 cap refusals |
| Native transcript independently replayed | Every source, ordinal, type, full offset and composed prefix accepted |
| Independently generated paths compared with native | All 818 full records identical, including complete cycle suffixes |
| Maximum observed depths | 62 nearest edges, 93 total edges |
| Maximum original prefix size | 144 decimal digits |
| Focused Python regressions using the newly generated native transcript | 80 passed, 0 errors/failures/skips |
| Pair-count, signed-cycle and full length bounds | Checked on all 818 paths |
| Full track reversal | Checked on 818 sources and all 4,728 edges |
| New reconstruction-delay control module | Compiled; 14 theorem axiom reports use only propext, Classical.choice and Quot.sound |

The **native stdout** SHA-256 is
`65acc78ac1e03747c254a2feb86fd1915d6941a67b99beffff7018130af2c3a6`. This exactly reproduces the archived
`native-attempt-2.log` digest. The independently generated **JSONL transcript**
has SHA-256 `125a6720fe751493bc5c02a48861d93eb5a898699cec1a156fae063a4dd13698`. These are different encodings and
must not be conflated.

The native and independent grid is `n in {7,8,12,31}`,
`J in {1,2,3,4,5,n+7}`, all exactly central `p,q in -2..2`, every admissible
signed W height, and `(p,q)=(100,-83),(-100,83)`. Root refinement, word size and
path length caps remain 256, 50,000 and 256 respectively. The independent
oracle needed at most 12 exact bisections; no cap was exhausted except in the
explicit refusal controls.

## Controls and exact bounds

For every one of the 818 paths, the independent control script verified

- `B=(n+7)(abs(p)+abs(2p+q+r)+1)`;
- nearest-prefix depth at most `K=(2B+1)^2`;
- the full signed W shape at the declared cutoff;
- `J*abs(H)<=n-1`;
- cycle suffix length exactly `2H` for J>=3, `2H+1` for J=2,
  3 for J=1,H=1, and `2H-1` for J=1,H>=2 (zero height has empty suffix);
- suffix length at most `2H+1` and at most `2n-1`;
- total length at most `K+2n-1`;
- swapped indices, complete target negation, local prefix exchange and final
  original-prefix exchange under source reversal.

The largest observed signed-cycle height is 18, with suffix depth 35.

**Both initial coordinates are necessary.** At `n=7,J=1`, the exact central
source `(0,1000,-917)` selects gap 3 and literal RUN indices `(4,1)`, producing
central target `(83,83,-339)`. The full reserve is 1176. Dropping the second
initial scalar coordinate gives reserve 14, already violated by the next first
coordinate 83. Source, target, local prefixes and oracle source hash are
retained in `extra-controls.json`.

**A scalar pair does not reconstruct the source.** The central source
`(1,2,-5)` has transformed initial pair `(1,1)` but is not any full W packet.
The actual `(1,1)` edge reaches `(-1,-3,6)=-W_1`; the full packet appears one
step later. The new Lean module proves this for every `Family n 1 beta`,
including strict centrality, the precise edge and rejection of every initial
full W shape. Setting the independent transcript cutoff to zero is refused.

**Nearest recurrence is not itself a zero-finiteness theorem.** The actual
`n=7,J=1` nearest selector alternates `W_4` and `-W_4` without hitting zero.
A different literal cycle exit reaches zero in 7 edges. The synthetic strict
half-tie control has error exactly 1/2 and is refused; it is explicitly not
an integral input of the irreducible literal family. The J<=4 actual coefficient
reserve has negative sign, preserving the need for the shear argument rather
than importing absolute contraction throughout the upper chamber.

## Independent source review

No mathematical blocker was found in the local central-orbit, bounded-tail
and completion assembly sources.

The actual orbit updates all three integral coordinates and derives its scalar
sequence from `-Packet.delta[0]`. Its nearest-gap input is itself the physical
value of a full inflated integer vector, so the previously proved cubic
no-half-ties result applies. A centrality invariant supplies actual RUN marks
at every depth. The full reconstruction equation begins at the first child,
and the cycle source is identified at N+1.

The original existential tail theorem did not expose a bound on N. The new
bounded-pair module addresses that distinction using K+1 actual pairs and
retains the same bounded N through both high-J and low-J classification. The
strict amplitude bound derives the literal cycle height range. Prefix and
cycle paths concatenate at the identical complete packet; original MarkTrace
witnesses and incidence identities are recomposed for the concatenation.

The resulting existential path theorem need not identify the executable's
first zero or first W cutoff. The executable verifier enforces its own earlier
stopping policy, and the formal zero-source case has a separate empty-path
endpoint. This is not a claim of general implementation refinement. Final
combined proof acceptance remains the root agent's separate source-bound
build and audit; this review's own formal receipt audits only the 14 new
control theorems.

## Formal control module

`PscVerif.ClassAPlusUpperCentralControls` has source SHA-256
`f22bcfc4ecad9d0645744dde67bc728afc2d441d03996dcda60533f1625e7402`. Main endpoint:

```lean
reconstruction_delay_control
  {n : ℕ} {β : ℝ} (hp : Family n 1 β) :
  Central n β source ∧ source ≠ cyclePacket 1 ∧
  (-source.delta 0, 2*source.delta 0+source.delta 1+source.delta 2) = (1,1) ∧
  IndexedDigitStep (upperSigma n 1) source 1 1 (signedSource true 1) ∧
  Central n β (signedSource true 1)
```

`source_not_full_cycle` excludes every signed integer height, and
`strict_reconstruction_prefix` supplies the one-edge OrderedInteriorPath.
The existing nonzero-cycle and half-tie controls remain named audit endpoints.
The two cosmetic warnings in the initial draft were removed. The clean build
log still contains inherited dependency warnings, with none from this module.

## Runtime and replay

Python 3.12.14; pixi 0.84.2; Mojo 1.1.0.dev2026090805 (34562fa1);
Lean 4.34.0-rc2; pytest 9.2.0. Use fresh output directories on replay; the
oracle and supplementary control script refuse to overwrite their outputs.

Working directory: `/workspace/scratch/c388c36ccd77/psc-upper-entry/kernel`

```sh
MODULAR_TELEMETRY_ENABLED=0 MODULAR_CRASH_REPORTING_ENABLED=0 /workspace/scratch/402f1bb377be/psc-ray-runtime/pixi/pixi run --locked mojo run -I . tests/test_class_a_plus_upper_recurrence.mojo --emit
```

Working directory: `/workspace/scratch/c388c36ccd77/psc-upper-entry`

```sh
python3 oracles/python/class_a_plus_upper_recurrence_independent.py --output-dir /workspace/scratch/c388c36ccd77/checks/central-completion/independent
```

Working directory: `/workspace/scratch/c388c36ccd77/psc-upper-entry`

```sh
python3 oracles/python/class_a_plus_upper_recurrence.py --native /workspace/scratch/c388c36ccd77/checks/central-completion/central-native.txt
```

Working directory: `/workspace/scratch/c388c36ccd77/psc-upper-entry`

```sh
PYTHONPATH=/workspace/scratch/402f1bb377be/psc-ray-runtime/python-checks PSC_UPPER_CENTRAL_NATIVE=/workspace/scratch/c388c36ccd77/checks/central-completion/central-native.txt python3 -m pytest tests/test_class_a_plus_upper_recurrence.py tests/test_class_a_plus_upper_recurrence_independent.py -q --junitxml=/workspace/scratch/c388c36ccd77/checks/central-completion/regression.xml
```

Working directory: `/workspace/scratch/c388c36ccd77/psc-upper-entry`

```sh
python3 /workspace/scratch/c388c36ccd77/checks/central-completion/verify-central-extra-controls.py --root /workspace/scratch/c388c36ccd77/psc-upper-entry --native /workspace/scratch/c388c36ccd77/checks/central-completion/central-native.txt --transcripts /workspace/scratch/c388c36ccd77/checks/central-completion/independent/exact-transcripts.jsonl --output /workspace/scratch/c388c36ccd77/checks/central-completion/extra-controls.json
```

Working directory: `/workspace/scratch/c388c36ccd77/psc-upper-entry/proof/PscVerif`

```sh
/workspace/scratch/b5ec043e7cbe/psc-toolchain/bin/lake build PscVerif.ClassAPlusUpperCentralControls
```

Working directory: `/workspace/scratch/c388c36ccd77/psc-upper-entry/proof/PscVerif`

```sh
/workspace/scratch/b5ec043e7cbe/psc-toolchain/bin/lake env /workspace/scratch/b5ec043e7cbe/psc-toolchain/bin/lean /workspace/scratch/c388c36ccd77/checks/central-completion/CentralControlsAudit.lean
```

Exact command receipts, source hashes and artifact hashes are in
`central-review-summary.json`. Universal BH, residual A1′ and general C4
are outside these finite replay results and this specialized proof review.
