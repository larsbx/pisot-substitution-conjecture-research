# Even-determinant rank two: verified progress and the remaining obstruction

Research starting point: `c0231e0fd64d9eee7f7bb798042d9966276e4cd6`.
Integrated main: `017969364269c116aaa5873bfcba6c9f1b1ba7e5`.

The research starting point includes the odd-stack exclusion (#617), concrete
solenoid realization (#618), even-stack residue (#619), and derived Pisot
contraction (#620). This investigation starts from all four. It does not
relabel #619's nilpotent reduction or its 96 finite controls as new work.
The local proposal also incorporates #621's target topology and has been
recompiled and audited against that revision.

**Strongest new formal result:** for every `r >= 3`,
`sigma_r = (1,2,100 2^r 1)` has no finite strict system, by explicit literal
witnesses and the existing cut-pair theorem. The even parameters `r >= 4`
form an unbounded-image-length PIP3 family satisfying the nilpotent and
complete-square necessary conditions. This does not assign them coincidence
rank two. The arbitrary even-determinant case remains open.

## Work shown

### Assumptions and hypotheses

The general reduction assumes primitive three-letter irreducible Pisot
incidence, actual coincidence rank two, a strict system with its stated
realization properties, and the published stack, covering and cohomology
inputs. Its geometric consequences remain written mathematics.

The new family exclusion has only the explicit word parameter bound.
The new solenoid theorem assumes only the nilpotent matrix equation on
the existing realization solenoid. The new cycle coefficient lemmas are
finite combinatorics, independent of a tiling interpretation.

The integrated #621 proves compact Hausdorff topology on the target,
a shift homeomorphism and joint continuity of its flow. Ordinary-hull
topology, continuity of desubstitution and realization from that hull,
normalized BBK/MEF identification, recognizability, finite fibres and BDS
periodicization remain separate inputs or obligations. The new halving
theorem uses the unchanged algebraic solenoid model.

### Derivation / reduction

#### Exact parity audit

| Argument | Valid without odd norm? | Retained dependency |
| --- | --- | --- |
| Eventual-range cycles and the three-dimensional winding kernel | Yes | Nonsingular irreducible cubic incidence; the connected eventual-range formula and the written winding construction. |
| Grouping endpoint germs into at most two classes per side | Yes in the even strict rank-two setup | W2's singleton fibre, W4's nonunit multiple fibre, directional extraction, periodicization, and branch location in an injective endpoint direction. |
| Four grouped cycle entries `(c,-c,-c,c)` | Yes | Zero row and column sums; this is finite algebra checked by the existing Lean theorem. |
| Winding rank at most one on pullbacks | Yes | The factor identifies the specified seam classes; the grouped graph is not asserted to present the quotient. |
| Injectivity of the stack cohomology pullback | Yes over rational coefficients | Barge (2015), Proposition 19, after the stated proper rewriting and stack construction. |
| Stack upper bound `dim H^1(X;Q) <= 4` | Yes | The preceding inputs. |
| Complete `K_{2,3}` or `K_{3,2}` covering obstruction | Yes | Explicit covering lift and separation hypotheses. Even nonunit directional extraction does not need this additional covering exclusion. |
| Original cycle-rank lower bound `beta_1(ER) >= 2` | Not from the odd-norm theorem at even norm | It must not be used to discard the square or one-cycle incomplete graphs. |
| Stack lower bound `dim H^1(X;Q) >= 5` | No available transfer | Barge's Theorem 22 requires odd norm in Lemma 20's modular eventual-rank argument. |

In that last argument an ordered-pair incidence matrix has blocks
`[[A,B],[B,A]]`. Odd norm ensures that `A+B` retains at least the Pisot
degree in eventual rank modulo two. The congruence `A-B = A+B (mod 2)`
then forces the second rank contribution. This step has no such guarantee
in the nilpotent even case. See [Barge (2015), Lemmas 20–21 and Theorem 22](https://www.numdam.org/item/10.24033/bsmf.2691.pdf).

The already merged [#619 proof](c4-even-stack-residue-2026-11-19.md)
uses the two-sheet cover `p:X->Y` and the integral eigenfunction theorem
to obtain

```text
dim H^1(Y;Q) = dim H^1(X;Q) = 4,
H^1(X;Q)^- = 0,               (M mod 2)^3 = 0.
```

It also requires a nonzero grouped seam square and an odd winding on a
periodic homoclinic pair of `Y`. The source theorem on torsion-free cokernel
is [Barge–Kellendonk–Schmieding, Theorem 5](https://arxiv.org/pdf/1204.1432).
Its cokernel statement applies to the maximal equicontinuous factor's
eigenfunction inclusion, not an arbitrary covering pullback.

#### Complete ranges and the finite controls

For a complete connected range `K_{a,b}`, the cycle rank is
`(a-1)(b-1)`. In the cubic setting the original rational cohomology
dimension is `3+(a-1)(b-1)`. Thus `K_{2,2}`, `K_{2,3}`, `K_{3,2}` and
`K_{3,3}` have dimensions `4,5,5,7`; a one-vertex side has cycle rank zero.
These dimensions concern the original hull, not the stack quotient.

The standing corpus exhausts PIP3 substitutions on three labelled letters
with nonempty image lengths at most three. It has 4,554 specimens, of which 1,926
have even determinant and 564 have positive eventual-range cycle rank.
The nilpotent filter retains the existing 96 specimens. The new original
graph classification is:

| Original eventual range | Cycle rank | Original `dim H^1` | Count |
| --- | ---: | ---: | ---: |
| `K_{2,2}` | 1 | 4 | 24 |
| `K_{2,3}` minus one edge | 1 | 4 | 6 |
| `K_{2,3}` | 2 | 5 | 24 |
| `K_{3,2}` minus one edge | 1 | 4 | 6 |
| `K_{3,2}` | 2 | 5 | 24 |
| `K_{3,3}` | 4 | 7 | 12 |

The canonical Mojo regression and independent Python oracle agree. All
288 unordered letter pairs retain the earlier exact/literal witnesses at
levels one through seven. The shape census is exhaustive only within this
declared corpus. It proves no classification at arbitrary image length.

In particular, 84 original graphs are complete and 12 are incomplete.
The control `01/211/102` has edges
`{(1,0),(1,1),(1,2),(2,1),(2,2)}`. Grouping columns `{0,1}/{2}` produces
a square, even though the original graph is not complete. This illustrative
grouping does not compute its actual stack quotient.

#### An unbounded literal exclusion

The [companion-family proof](c4-even-companion-family-2026-11-19.md)
extends the earlier `1/2/10022221` control. With
`w=100 2^r 1`, the level-three words are

```text
sigma_r^3(1) = 211 w^r 2,
sigma_r^3(2) = w 22 (211 w^r 2)^r w.
```

The prefixes `211 w 10022` and `w 22211100` both have Parikh vector
`(4,5,r+3)` and are followed by `2`, for every `r>=3`. Pairs `02` and `01`
have witnesses at levels one and four. Lean proves the literal statements
and then `Psc.EvenCompanion.no_strict_system`, quantifying over every finite
strict system. Neither this proof nor its strict-system conclusion assumes
coincidence rank two or a geometric realization.

The uniform PIP3 membership, nilpotent parity, complete square and original
cohomology dimension four are proved separately in the note. The root
argument is written mathematics; bounded exact PIP replay is recorded.

#### Two additional invariants, with their limitations

1. **Integral seam cycles.** On a ternary bipartite graph, every simple
   cycle has four or six edges. Lean checks all Boolean group assignments
   and proves that a nonzero grouped coefficient is `1` or `-1`.
   Integral simple-cycle decomposition then gives a written consequence:
   a nonzero grouped cycle map is surjective over the integers. An
   eight-cycle on four vertices per side maps to twice the generator and
   is a sharp countercontrol. See [integral seam note](c4-even-seam-integrality-2026-11-19.md).
2. **Unique halving of the solenoid.** Lean constructs `B` from
   `(M mod 2)^3=0`, proves `M^3=2B` and `MB=BM`, and defines
   `H(z)_n=B z_(n+3)`. It proves `2H(z)=z` and `H(2z)=z` on the existing
   concrete solenoid. There is therefore no nonzero point of order two.
   See [solenoid note](c4-even-solenoid-2026-11-19.md). The genuine stack
   deck map fixes the solenoid image, so this does not exclude that map.

The algebraic consistency control makes the remaining integral issue
explicit. With a torsion-free, uniquely two-divisible group `E` of rational
rank three, take

```text
H_X = H_Y = E direct-sum Z,
p*(e,n) = (e,2n),          transfer(e,n) = (2e,n).
```

Both transfer identities hold, the two rational dimensions are four,
the eigenfunction subgroup is saturated, and the extra class can have a
primitive source seam image. Nevertheless `coker p* = Z/2`. Thus an odd
winding downstairs can lift to twice a class upstairs. This is an
algebraic control, not a PIP3 substitution or a strict counterexample.

### Evidence and replay

The proposed source includes four new Lean result modules, a canonical
`StrictSystemCore` extraction, a compiled-axiom audit entry point, the Mojo
family certificate and regression, the original-range shape extension, and
an independent Python oracle. The extracted 397 lines retain the exact
baseline statements and proof bodies; the remaining `StrictSystem` source
changes only its import. The focused compiled closure has 21 local modules,
483 source-named proofs and all 49 new named proofs. The audit checks 1,106
declarations, including 804 theorem declarations after generated helpers.
It accepts only `propext`, `Classical.choice` and `Quot.sound`. The full
legacy sector aggregate and repository-root Lean library were not rebuilt
in this focused replay. The [integrated evidence packet](../evidence/even-rank-two-pr621-2026-11-19/README.md)
records exact source hashes and the build and audit after #621. The
[original evidence packet](../evidence/even-rank-two-2026-11-19/README.md)
preserves the earlier completed verification and finite replay unchanged.

```sh
cd proof/PscVerif
lake --no-cache build PscVerif.EvenCompanionFamily PscVerif.EvenSeamCycles PscVerif.PeriodicPartnerEvenSolenoid
lake env lean EvenRankTwoAudit.lean
```

From the repository root:

```sh
python3 tools/make_proof_bank.py --check
python3 tools/make_ledger.py --check
PYTHONPATH=tools python3 -m claim_governance.cli --root .
python3 oracles/python/even_companion_family.py --corpus-shapes
(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_even_companion_family.mojo)
(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_c4_even_stack_residue.mojo)
```

The aggregate evidence summary distinguishes successfully compiled local
results from hosted checks on the baseline. The proposed changes have not
been published and have no hosted CI result of their own.

### Negative controls

- The original graph can be incomplete while its grouped image is square.
- The uniform level-three family witness fails at `r=2`; a separately
  replayed level-four witness exists there.
- Eight-edge cycles can have grouped coefficient two outside the ternary
  bound.
- The Thue–Morse solenoid also has unique halving; its published two-sheet
  cover has dilation of algebraic degree one and reducible incidence, so it
  remains outside PIP3.
- The integral index-two model satisfies the listed cohomological data
  without producing a fifth rational class.

### Non-claims / remaining gaps

No replacement universal lower bound of five was proved, and no explicit
strict counterexample in the target PIP3 class was found. The next general
obligation is to exploit the literal cubic presentation to exclude the
periodic odd winding with four seam lifts, or to prove an independent
strict-system exclusion for arbitrary nilpotent cubic substitutions.

If an integral approach is pursued, it needs a new justified constraint
on the actual composite factor and its index-two class; rational stack
injectivity and saturation of the eigenfunction subgroup do not supply it.
Any proposed stronger saturation statement must survive the controls above.
Recognizability, finite-fibre and periodicization inputs of the general
geometric chain also remain distinct from the proved finite/local Lean
results. Universal C4, higher coincidence ranks and PSC remain open.
