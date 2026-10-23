# Accepted class-D hitting certificates and scoped G1 — 2026-10-22

**Status:** derived corollary of the accepted `ClassDBoundaryHitting` scope
and the existing half-coincidence-to-BPA implication. Independent human
review remains pending. This note adds no executable mathematical mechanism,
spectral import or universal claim. The scoped corollary is registered as
`ClassDFiniteBPA`; no existing claim status is promoted.

| Claim | Governed status |
| --- | --- |
| Scoped finite BPA | Repository-proved: `ClassDFiniteBPA`; determinant-two class-D normal form only; derived from accepted all-seed hitting and the existing half-coincidence implication; human review pending |

PR #277 integrated both residual `b=0` certificates. PR #298 subsequently
recorded complete class-D integration, including the positive-`b` interiors,
at accepted source tree `c325aa5345e1f49b2fb50b37565bd2902104aab7`.
The [assembly audit](class-d-assembly-audit-2026-10-21.md) and
[CI acceptance packet](../evidence/class-d-integration-accepted-2026-10-21/)
are the acceptance sources. Earlier packets' candidate and local-runtime
limitations remain truthful historical records; they are not current gates.

## Assumptions and hypotheses

Use the determinant-two class-D normal form in the ordered alphabet `(x,c,y)`:

$$
x\mapsto xy^pc,\qquad c\mapsto cy^qx,\qquad y\mapsto cy^rc,
\qquad p-q=s\in\{-1,1\}.
$$

The parameters are nonnegative integers and the substitution is primitive
irreducible Pisot (PIP). The overlap graph is the canonical union of all
three swap-seed closures. Displacement is bottom start minus top start;
each ordered occurrence edge obeys

$$w'=Mw+\pi(\text{bottom prefix})-\pi(\text{top prefix}).$$

All geometry uses strict interior overlap and Perron lengths. A target has
`w=0`; its top and bottom letters need not agree. Parameters stay fixed
throughout each path. No seed-legality, unimodularity, finite-injectivity or
realized-tiling hypothesis is added. Rational independence of Perron lengths
is the derived irreducibility fact used by Proposition 4 below, not a new
independent assumption.

## Targeted literature stop/go

Decision: **proceed with the existing implication specialized to its accepted
class-D premise**. No new universal invariant or diagnostic is proposed.
The [October 2 gate](bpa-overlap-depth-literature-gate-2026-10-02.md) is reused;
the following primary-source passages were rechecked for this specialization:

| Source | Transfer and limit |
| --- | --- |
| [Sirvent–Solomyak (2002), Theorem 5.6](https://doi.org/10.4153/CMB-2002-062-3) | Half-coincidence gaps and BPA termination are the existing mechanism. Its legal fixed-point-prefix setting is transferred to repository swap seeds by the already-proved Proposition 4, rather than assumed identical. |
| [Akiyama–Barge–Berthé–Lee–Siegel, §5.3](https://www.irif.fr/~berthe/Articles/AkiyamaBargeBertheLeeSiegel.pdf) | Termination **with coincidence** is the spectral criterion. Finite BPA alone supplies no such conclusion. |
| [Martensen (2004), Example 3.5](https://topology.nipissingu.ca/tp/reprints/v28/tp28111.pdf) | Changing to a non-Perron length vector can change termination. Retain PIP, Perron lengths and the existing balanced-cut argument. |

The new contribution is the explicit class-D corollary and reconciliation
of its acceptance scope, not a new termination theorem or literature import.

## What the occurrence-compatible templates establish

For `b=0`, the two families are

| Branch | `(p,q,r)` | Symbolic tail | Complete finite prefix | Tail vertices / directed support | All-seed hitting bound |
| --- | --- | --- | --- | --- | --- |
| minus | `(3a+5,3a+6,2a+4)` | `a>=4` | `a=0..3` | 145 / 781 | `K<=4` |
| plus | `(3a+3,3a+2,2a)` | `a>=7` | `a=0..6` | 718 / 4,326 | `K<=6` |

These are all-parameter theorems from
[the family note §§4i–4m](p1b-boundary-hitting-progress-2026-10-08.md),
not extrapolations from the eight original graphs. In each tail, integral
labels identify the seed-generated graph with fixed simple directed support.
Multiplicity and whole-image occurrence indices are not asserted constant.
The minus selected-edge cover additionally starts at `a>=2`; it does not
assert equality of the full support there.

The construction splits each image into first letter, run and last letter.
For a proposed child offset, the recurrence fixes an affine run-index
difference `m=k_bottom-k_top`. When both segments are runs, legal positions
exist exactly when

$$-(n_{top}-1)\le m\le n_{bottom}-1.$$

They can be chosen as `k_top=max(0,-m)`, `k_bottom=max(0,m)`; with one run,
the non-run index is zero and the corresponding interval endpoint is zero.
Exact signs prove interiority and these guards throughout the tail. The
all-child calculation proves closure and the exact seeds initialize the
reachability induction. Thus a template edge lifts to actual occurrences
for each fixed parameter; the next edge starts from exactly its resulting
typed offset. Composing lifts does not splice incompatible offsets or
change the parameter. The finite prefixes use the exact uncapped graphs,
including the plus empty run at `a=0`.

Reverse target distance is a nonnegative integer rank. Every positive-rank
vertex has **some** legal edge decreasing rank, so iteration reaches a
target within the displayed bound. There is no assertion that every edge
decreases rank or every infinite path must visit a target.

## Scoped G1 corollary and explicit bounds

**Corollary.** For every PIP member of the determinant-two class-D normal
form above, the repository balanced-pair automaton from all three swap
seeds is finite. If `K_sigma` is the maximum first offset-zero depth on
its all-seed graph and `L=max(p+2,q+2,r+2)`, every reachable balanced pair
`(u,v)`, at every inflation level, satisfies

$$|u|=|v|\le H_\sigma:=2L^{K_\sigma+2},\qquad
|B_\sigma|\le\frac{9^{H_\sigma+1}-9}{8}.$$

In particular, valid integer upper bounds on the two full `b=0` branches are

$$H_-(a)=2(3a+8)^6,\qquad H_+(a)=2(3a+5)^8\quad(a\ge0).$$

*Proof.* The accepted class-D assembly supplies an offset-zero descendant
for every seed-reachable vertex. The seed graph is finite by
`SwapOverlapFiniteness`, so `K_sigma` is finite. Apply Proposition 4 and
Corollary 5 of the [overlap-depth note](bpa-termination-by-overlap-depth-2026-10-02.md)
to every swap seed. Their hypothesis is half-coincidence, so aligned
strong coincidence is unnecessary for this conclusion.

For completeness, at levels `n>=K_sigma` Proposition 4 gives symbolic
length at most `2 beta^K_sigma ell_max/ell_min`. Primitivity on three
letters gives an occurrence path of at most two edges between any two
letters. The Perron relation along that path gives
`ell_max/ell_min<=beta^2`, and the column-sum bound gives `beta<=L`.
For `n<K_sigma`, a balanced piece lies in a seed inflation of side length
at most `2L^n`. Both cases are bounded by `H_sigma`. There are at most
`9^m` ordered pairs of ternary words of side length `m`; summing gives the
stated state bound. For `b=0`, substitute `L=3a+8,K_sigma<=4` on minus
and `L=3a+5,K_sigma<=6` on plus. These are deliberately coarse bounds. ∎

For positive `b` and the inherited large-`r` wedges, use the finite depth
of the accepted component for the chosen substitution; no branch-wide
constant is asserted here. This corollary is scoped G1, not the universal
`G1` ledger node. It uses neither a spectrum theorem nor an assumption that
the seed graph equals the full realized-tiling overlap graph.

## Negative controls and quantifiers

- The spectral result `-1<lambda_d<-1+1/d` for `d=a+2>=4` is unchanged.
  It refutes a parameter-independent contraction margin. It does **not**
  refute the now-proved bounds `K<=4,6`, obtained by another mechanism.
  Nor do those depth bounds make the displayed word-length bounds constant.
- Eventual hitting is `for every parameter, for every reachable vertex,
  there exists a finite target path`. The template proves the stronger
  uniform depth statement only on its declared `b=0` branches. None of
  these statements quantifies over every choice of outgoing edge.
- In the pinned minus comparison, 486 edges from positive ranks fail to
  descend. Requiring all edges to descend would reject a productive graph.
  Full support differs at `a=2,3` (779 versus 781 edges), although the
  selected-edge cover works at both. A vertex plateau is insufficient.
- The fitted index `9-a` passes `a=2..8` and later becomes negative.
  The affine guard checker rejects it. Equal vertex sets with a deleted
  edge, lowered tail floors, capped graphs, corrupted ranks and offsets
  remain rejection controls in the existing regressions.
- Zero offset with distinct letters is a half-coincidence, not a terminal
  equal-letter coincidence. The corollary therefore does not establish
  productivity, `SC_all`, Ω's PDS conclusion or general PSC.

Universal #138, #139, #84 and G1 remain open. The class-A/C work in the live
roadmap is a separate coverage problem; this note does not reopen accepted
class D or extend its certificate to those regions.

## Evidence and replay

The dependency registration uses exactly `ClassDBoundaryHitting` and
`SwapOverlapFiniteness`. Proposition 4 is instantiated on the class-D
premise in the proof above. It is not registered as depending on the
universal `G1HalfCoincidenceRoute`, which bundles that implication with an
open all-PIP premise; the existing `PDSImpliesRepoG1` registration uses the
same distinction. There is no implication back from `ClassDFiniteBPA` to
`G1`, to universal boundary hitting, or to a spectrum assertion.

The generated Open model establishes `ClassDFiniteBPA` while retaining its
`G1NotEstablished` and `PDSNotEstablished` invariants. Regression controls
make either hitting or graph finiteness open and check that the scoped
conclusion then becomes conditional and unreachable. A TLC mutation adds
the false invariant `ClassDFiniteBPANotEstablished` and must exhibit its
violation. These are checks of dependency wiring, not a Lean formalization
or a new execution of the mathematical certificate.

The [dependency-validation packet](../evidence/class-d-g1-ledger-2026-10-22/)
records fresh local TLC execution, source pins and replay instructions.

```sh
python tools/make_ledger.py --check
python tools/make_proof_bank.py --check
TLA_TOOLS=/absolute/path/to/tla2tools.jar python -m pytest -q tests/test_ledger_generation.py
TLA_TOOLS=/absolute/path/to/tla2tools.jar ./proof/tla/check.sh
```

Canonical authority remains the unchanged Mojo certificate:
`kernel/psc/class_d_boundary_template.mojo` (`certify_boundary`),
the selected-edge checker, and the accepted assembly components. In the
locked environment, the relevant boundary commands are:

```sh
cd kernel
pixi run mojo run -I . tests/test_class_d_boundary_template.mojo
pixi run mojo run -I . class_d_plus_boundary_certificate.mojo
pixi run mojo run -I . tests/test_class_d_minus_certificate.mojo
```

The complete native source/runtime/CI identities are preserved in the
accepted packet; no fresh native execution is implied by this note.
From the repository root, replay source/receipt provenance and independent
certificate controls with:

```sh
python tools/check_class_d_assembly_evidence.py
python tools/check_class_d_integration_ci.py
python -m pytest -q tests/test_class_d_boundary_template.py tests/test_class_d_plus_template.py tests/test_class_d_minus_certificate.py tests/test_class_d_integration_ci.py
```

The graph cap is 20,000. Symbolic undecided signs/guards and exhausted
budgets refuse a certificate. The historical acceptance, current replay
results and any local skips have separate provenance; a green Python replay
is not a replacement for canonical execution.
