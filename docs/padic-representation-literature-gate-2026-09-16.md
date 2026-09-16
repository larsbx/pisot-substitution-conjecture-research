# Literature gate — a real times p-adic box carrier

## Proposed step

Round-two item R7 carries a "p-adic module" as one of its four parts, inherited
from round-one item B7, "shared real times 2-adic box kernel". B7's state line
records the gap precisely: `mojo/psc/finite_cokernel_address.mojo` computes
`Z^3 / M^k Z^3` classes exactly, and there is no p-adic module in
`larsbx/finite-math-kernels`.

The proposal is therefore a carrier in that monorepo:

1. exact `Z_p` arithmetic at a declared precision `k`, as a residue together
   with the ball radius `p^(-k)` it stands for;
2. a combined box, one closed rational interval per Archimedean coordinate and
   one `p`-adic ball per finite place;
3. the same fail-closed discipline the rational intervals already carry, where
   unknown containment or sign is never promoted to equality.

This review asks whether that carrier is a known construction, which of its
hypotheses transfer to the standing PIP regime, which known families break a
naive version, and — the question that turned out to matter — whether the step
it serves is the next one.

No PDF snapshots were imported for this review, so there is nothing under
`docs/source-imports/` to cite. The entries under [Sources](#sources) are
bibliographic references to standard literature, not verified snapshots.

## Decision

**Proceed with the carrier only. Do not invoke it, and do not rank it as the
next theorem step.**

Two separate findings support splitting the item this way.

The carrier itself is standard and is legitimate infrastructure: representing
`Z_p` to finite precision with an explicit ball radius is ordinary zealous
`p`-adic arithmetic, and it is the exact analogue of what
`finite_exact/closed_interval.mojo` already does for the reals. Building it
asserts nothing.

The theorem step it exists to serve is **not** next, and this gate exists to say
so before the work is spent. See finding 4.

## Findings

### 1. The finite-place factor is not optional in this regime, and that is settled

For a non-unit Pisot substitution the representation space is not Euclidean.
Siegel gives the representation of non-unimodular substitutive dynamical
systems with the finite-place factors present,[^1] and Minervino and
Thuswaldner construct the Rauzy fractals in a space contained in an open
subring of the adele ring.[^2] The survey of the Pisot substitution conjecture
states the unimodular and non-unimodular settings separately for this
reason.[^3]

The standing regime is the non-unit one: the canonical determinant-two
regression has `|det M| = 2`, and `finite_cokernel_address.mojo` already
observes the consequence, a cokernel `Z^3 / M^k Z^3` of order `2^k`. So the
2-adic component of that repository's own diagnostic is not a refinement anyone
chose; it is what the regime forces.

This is the firewall the repository already maintains, and it is the one part of
this proposal that needs no further argument.

### 2. What transfers is the carrier, and only the carrier

Three things transfer cleanly.

- **Finite precision with an explicit radius.** A `p`-adic number known modulo
  `p^k` is a ball of radius `p^(-k)`, and arithmetic on such balls is standard
  zealous `p`-adic computation, with the loss of precision under division and
  under Hensel lifting well understood.[^4] Nothing here is new.
- **The conservative-filter contract.** A `p`-adic ball is the same kind of
  object as a closed rational interval: it may certify a difference is non-zero,
  and it may return unknown, and the second must never be read as the first.
  `docs/rational-interval-arithmetic-spec.md` in the monorepo already fixes that
  contract, and the `p`-adic side should inherit it verbatim rather than invent a
  second one.
- **The addressing.** Dumont--Thomas numeration is the standard addressing of
  prefix data for substitutions,[^5] and the repository's exact renewal
  addresses already mirror it, so the carrier has a caller-side language.

### 3. What does not transfer is every conclusion

- **The unimodular geometric theory.** Barge and Kwapisz prove a geometric
  theory of *unimodular* Pisot substitutions.[^6] Its conclusions are not
  available at `|det M| = 2`, and the repository's existing refusal to replace
  the internal image by a Euclidean stable lattice is correct.
- **Tiling and separation in the adelic setting.** Having the representation
  space is not having a separation property in it. The constructions in the
  non-unit setting carry their own hypotheses, Meyer and coincidence conditions
  among them,[^2] [^3] and `docs/p1-overlap-affine-pump-literature-gate-2026-09-15.md`
  already recorded that PR #91 must treat the complete representation space as a
  candidate setting rather than an available property. That finding stands and
  this gate does not weaken it.
- **Computability as evidence.** No result licenses concluding productivity, or
  excluding a zero-shift-free cycle, from the fact that one can compute in the
  representation space. A carrier that can evaluate a difference exactly is not
  an argument that the difference is non-zero.

### 4. The step this serves is not the next step

This is the finding that changed the decision, and it comes from the
repository's own surfaces rather than from the literature.

`docs/completion-ledger-2026-09-14.md` states the shortest route and its single
open premise, overlap productivity for one swap seed, and then names the next
open obligation: context-preserving recognizability **plus** separation in the
full non-unimodular internal representation.

`docs/p1-overlap-collar-2026-09-16.md` then settled the first half in the
negative direction. The radius-`m` collar recursion is exact, the
determinant-two graph has separation radius `1`, and the golden pump lifts to a
collared cycle at every tested radius, so bounded-context equality cannot by
itself exclude zero-shift-free recurrence. The ledger records what that leaves:
**the splicing and tiling-dictionary bridge remains open.**

The affine-pump gate's revised program is explicit about the order. Its step 5,
the non-unit representation step, is to be invoked "only for context-compatible
survivors". Step 4, the seed-relative growth bridge, is the open one. So the
`p`-adic module is a step-5 tool while step 4 is unsettled.

The consequence is not "stop". A carrier is not a step, and a kernel that exists
before it is needed is better than one improvised under argumentative pressure.
The consequence is that **building it must not be reported as progress on
overlap productivity**, and that R7's ranking of it alongside the other three
parts overstates its position in the route.

### 5. Negative controls the carrier must satisfy

| Control | Case | What it catches |
| --- | --- | --- |
| Unimodular substitution | `det M = 1` or `det M = -1` | the finite-place factor is trivial; a carrier that manufactures a non-trivial `p`-adic component here is wrong |
| A prime not dividing `det M` | `p = 3`, `det M = 2` | the `p`-adic factor is trivial, so using it is a category error, not a refinement |
| The determinant-two regression | `det M = 2`, `p = 2` | the cokernel has order `2^k`; this is the case the carrier exists for, and it must agree with `finite_cokernel_address.mojo` where they overlap |
| Precision exhaustion | a difference that is zero to precision `k` | must answer unknown, never zero: a ball containing zero is not the point zero |
| The golden zero-shift-free cycle | six edges, inside a productive graph | recurrence alone excludes nothing, and the carrier must not be presented as resolving it |

The third row is the one that makes the carrier checkable rather than merely
plausible: the existing exact cokernel diagnostic is an independent
implementation of the same finite quotient, so the two can be differentially
tested against each other where their domains meet.

## What this gate licenses, and what it does not

1. **Licensed:** an exact `Z_p` ball carrier and a combined real-times-`p`-adic
   box in the kernels monorepo, with a spec document beside
   `docs/rational-interval-arithmetic-spec.md`, inheriting its unknown-is-not-
   equality contract, and differentially tested against the existing exact
   cokernel diagnostic.
2. **Not licensed:** any separation, tiling, or unique-representation property in
   the representation space.
3. **Not licensed:** any statement that the carrier advances overlap
   productivity, the open premise of the shortest route, or the splicing and
   tiling-dictionary bridge.
4. **Not licensed:** reporting R7's p-adic part as delivered when the carrier
   lands. The carrier is the part that is available now; the step it serves is
   behind an open obligation, and the delivery ledger should say which of the two
   it is recording.

## Sources

[^1]: Anne Siegel, "Représentation des systèmes dynamiques substitutifs non unimodulaires," *Ergodic Theory and Dynamical Systems* 23 (2003), 1247–1273.
[^2]: Milton Minervino and Jörg Thuswaldner, "[The geometry of non-unit Pisot substitutions](https://doi.org/10.5802/aif.2884)," *Annales de l'Institut Fourier* 64 (2014), 1373–1417; [arXiv:1402.2002](https://arxiv.org/abs/1402.2002).
[^3]: Shigeki Akiyama, Marcy Barge, Valérie Berthé, Jeong-Yup Lee and Anne Siegel, "On the Pisot substitution conjecture," in *Mathematics of Aperiodic Order*, Progress in Mathematics 309, Birkhäuser, 2015, 33–72.
[^4]: Xavier Caruso, "[Computations with p-adic numbers](https://arxiv.org/abs/1701.06794)," *Les cours du CIRM* 5 (2017). Zealous, lazy and relaxed arithmetic, and precision loss.
[^5]: Jean-Marie Dumont and Alain Thomas, "Systèmes de numération et fonctions fractales relatifs aux substitutions," *Theoretical Computer Science* 65 (1989), 153–169.
[^6]: Marcy Barge and Jarosław Kwapisz, "Geometric theory of unimodular Pisot substitutions," *American Journal of Mathematics* 128 (2006), 1219–1282.
