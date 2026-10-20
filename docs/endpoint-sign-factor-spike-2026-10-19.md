# Exploratory spike: does the Branch-B sign gauge descend to letter endpoints? — 2026-10-19

**Status: executable hypothesis-discrimination experiment, not a proof.**
**Canonical implementation:** [\`kernel/psc/endpoint_sign_spike.mojo\`](../kernel/psc/endpoint_sign_spike.mojo); [\`kernel/prefix_suffix_sign_spike.mojo\`](../kernel/prefix_suffix_sign_spike.mojo); regression [\`kernel/tests/test_endpoint_sign_spike.mojo\`](../kernel/tests/test_endpoint_sign_spike.mojo).
**Predecessor:** [the prefix/suffix literature gate](branch-b-prefix-suffix-literature-gate-2026-10-19.md), [the CK-v3 side-route status](ck-v3-side-route-status-2026-10-12.md).
This note does **not** reassign the project’s primary #138/#139/#84 proof route.

## Assumptions and hypotheses

For each \(\sigma\) in the repository's *exactly screened* 4,554-member ternary PIP corpus, build its seed-reachable normalized balanced-pair automaton with a declared state cap. **Capped runs are inconclusive.** Identify each recurrent noncoincident SCC that is *closed among noncoincident descendants*; coincidence children are allowed and separately recorded. The condition “closed” in this experiment is **not** “nonproductive.”

For a noncoincident parent state \(s=(u,v)\), inflate both tracks and cut at every Parikh zero return into **raw, ordered** child occurrences \(w\). Let \(\overline w\) be the normalized child type, obtained by swapping tracks if necessary, and define the bit
\[
 b(s\to\overline w;\mathrm{occ})=
 \begin{cases}0&w=\overline w,\\1&w\ne\overline w.\end{cases}
\]
This is a deliberately chosen, order-dependent sign convention, identical to the one used in \`psc.derived_system\`. It is not permutation parity.

Let \(N_C^+(s,t)\), \(N_C^-(s,t)\) count occurrences with bit 0,1. Branch A is \(Q_C=N_C-|S_C|\ne0\) where \(S_C=N_C^+-N_C^-\). In the other components, the exact finite signed-graph Perron-compatibility algorithm (including **cyclic period wrap**) gives Branch B or C; no floating-point spectral threshold is fitted.

A *separate* open question is the Boundary-Injection Exclusion conjecture
\[
 \sigma_+,\sigma_-\text{ both bijective} \Longrightarrow
 \text{no closed recurrent Branch-B SCC}.
 \tag{BI}
\]
It is NOT proved by finding zero witnesses in a finite corpus.

## Derivation and the new connection tested

The classical prefix–suffix automaton records entire substitutions \(\sigma(a)=p\,b\,s\) and ancestor position data; the external pair endpoint maps \(\sigma_+,\sigma_-\) forget almost all of this. The proposed *endpoint holonomy* route requires the orientation cocycle to factor through a meaningful endpoint/context quotient.

First test the **coarsest** proposed quotient, the four external endpoint letters of a normalized balanced-pair state:
\[
 E(s)=(u_0,v_0,u_{|u|-1},v_{|v|-1}).
\]
Its exact base-\(3\) encoding is injective on ordered four-tuples and cannot confuse distinct profiles by hash collision. The spike has two *different* diagnostics:

- **Literal edge-label factoring:** if two actual child occurrences have the same \((E(s),E(t))\) but opposite \(b\)-bits, the sign cannot be a function solely of those endpoint-profile pairs. This obstructs a naive local endpoint-only cocycle; it does not obstruct a richer ancestor-context cocycle.
- **Branch-B vertex-gauge factoring:** when the entire SCC is Perron-compatible, compute the finite \(F_2\) gauge \(x_C\) from the existing \`finite_graph.signing.compatibility_potential\` routine. Check whether \(x_C(s)=x_C(t)\) whenever \(E(s)=E(t)\). On a strongly connected support the potential at fixed Perron phase is unique up to one global bit, so equality within fibers is gauge-independent. Failure shows **this particular gauge** cannot descend to four external endpoint letters. Success does not establish a natural geometric endpoint holonomy or (BI).

**Nonvacuity guard.** Gauge descent through (E) is automatically true when every state in (C) has a distinct four-letter profile. The driver therefore separately counts Branch-B SCCs with **duplicate** endpoint profiles, how many of *those* admit an endpoint-constant Perron gauge, and the maximum Branch-B SCC size. A gross gauge-success fraction without this denominator is not evidence for endpoint holonomy.

The same census records whether any Branch-B state has matching \(\sigma\)-image **first** or **last** letter. This is the SCC-Diagonal property, separate from BI: shared endpoint images somewhere in \(\sigma\) do **not** ensure a given SCC realizes the colliding pair. The spike can falsify the observed implication but never prove it universally.

## Finite quantifiers, exact replay, and budget accounting

Canonical run (requires the repository's pinned Mojo environment):

\`\`\`sh
cd kernel
pixi run mojo run -I . tests/test_endpoint_sign_spike.mojo
pixi run mojo run -I . prefix_suffix_sign_spike.mojo --limit 4554 --state-cap 20000
\`\`\`

The driver screens the same 4,554 ordered substitutions once using \`psc.corpus.pip_corpus()\` and passes each to the shared \`psc.bpa.build\`; it does not implement a competing PIP test, automaton, SCC algorithm, or sign solver. It emits \`ENDPOINT_SIGN_SPIKE_START\`, a single \`ENDPOINT_SIGN_SPIKE_RESULT\` summary and \`ENDPOINT_SIGN_SPIKE_COMPLETE\`. Explicit counts include visited/capped substitutions, the bi-injective subsample, closed SCCs split into A/B/C, bi-injective A/B/C SCCs, Branch-B SCC-Diagonal positive/negative, Branch-B endpoint-gauge descent positive/negative, and A/C literal endpoint-profile conflicts. Optional \`--witnesses\` emits every state of potentially decisive Branch-B components; the default avoids overwhelming CI logs.

The run in [\`.github/workflows/endpoint-sign-spike.yml\`](../.github/workflows/endpoint-sign-spike.yml) executes both the focused regressions and this full finite-domain spike on the pull-request head; its **raw stdout and stderr** are retained as Actions artifacts. Numerical tallies belong to those receipts and are not invented in this design note. If a build is capped, it is **not** counted as absence of Branch B.

The project census has only \(|\mathcal A|=3\) and each substitution image length \(\le3\). Even a complete run **does not explore alphabet 4** or the long-image perturbation family; conclusions must carry that selection limit.

## Exact micro-calibration (independent small oracle; Mojo replay required)

A separate, small, integer-only balanced-pair decomposition check of **trial 8381** gave a complete 11-vertex reachable graph. Its unique closed recurrent noncoincident SCC has **three states** and **five internal child occurrences**, **all five with negative orientation** relative to lexicographically normalized states. Its period is one, so the sign class is Perron-compatible with phase bit 1 (Branch B). It has an SCC-level endpoint diagonal, but the three states have **three distinct external four-letter profiles**. Consequently, a four-letter endpoint gauge test that reports "success" here is **vacuous**, not evidence for endpoint holonomy.

The new canonical **Mojo regression** now explicitly asserts these replay figures. The result is an independent local calibration, not a fresh large-corpus Mojo receipt; the CI job must verify the code and its numeric corpus totals before either is cited as confirmed by the repository. This is a concrete example of the reason to count `B_duplicate_profiles` separately.

## Negative controls

1. **Trial 8381:** \(1\mapsto132,\ 2\mapsto32,\ 3\mapsto21\); \(s=((2,3),(3,2))\). One inflation gives \((3,2,2,1)\mid(2,1,3,2)\) as one noncoincident block. No per-state productivity claim is legitimate, even for Branch B.
2. **Bi-injective endpoint control:** \(0\mapsto01,\ 1\mapsto12,\ 2\mapsto20\) has \(\sigma_+=(0,1,2)\) and \(\sigma_-=(1,2,0)\). Distinct *external* endpoints cannot synchronize under these permutations; internal return cuts are not thereby excluded. This is a word-combinatorial control and is **not asserted PIP**.
3. **Tribonacci:** the familiar \(0\mapsto01,\ 1\mapsto02,\ 2\mapsto0\) provides an actual PIP automaton with productive recurrent components. It prevents treating “recurrent” as “strict nonproductive.”
4. **Branch-A and Branch-C witnesses** remain controls for false universal sign-factor claims: sign-cancellation/strictness is not the same as Branch-B Perron compatibility.

## Non-claims and next gate

This code does not prove endpoint-injection exclusion, SCC-Diagonal, SCC Producer, any general strong-coincidence result, BPA finiteness, #138, #139, #84 or PSC. The experiment does not assume that an internal child's endpoint data is the image of its parent's external endpoint pair, nor does it treat a fitted vertex gauge as a canonical geometric object.

**After a green empirical receipt:** inspect actual bi-injective A/C components and any Branch-B **failure of four-letter gauge descent**. If the coarse factor fails, enlarge the quotient *only with proof-relevant data* (first internal Parikh-zero-return bracket, then a Canterini–Siegel paired prefix–suffix occurrence/ancestor record) and repeat the exact edge-class consistency test. Do not optimize a guessed endpoint-holonomy cocycle without first proving that its source-to-child mapping preserves the missing context.

**Acceptance bar:** an independently replayable Mojo counterexample or finite-domain table, correct graph/occurrence semantics, cap accounting, negative controls, and no theorem-status promotion.
