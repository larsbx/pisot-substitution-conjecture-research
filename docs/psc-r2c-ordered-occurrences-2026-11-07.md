# R2C ordered occurrence replay

## Work shown

### Assumptions and hypotheses

Fix a literal non-erasing substitution on 0, 1, 2 and a nonempty balanced seed. The domain is the child closure of that seed with its given top and bottom order. A complete row contains every interval between consecutive equal-Parikh prefix cuts in the two inflated tracks. Coincidences, exits and repeated children are included.

### Derivation / reduction

Use the canonical BPA zero-cut routine and both image-prefix-length arrays. Each child start has one parent index and offset on each track because images are nonempty. Breadth-first traversal interns literal ordered pairs. The child ordinal and absolute half-open interval distinguish parallel occurrences even when they have the same target. The sign is +1 for a child in canonical top/bottom order, −1 for its reverse, and +1 at a coincidence. A sign is an orientation datum rather than a rational R2 score.

### Targeted literature stop/go

Sirvent–Solomyak (2002), §3, supplies the irreducible BPA cuts, and Martensen (2004), §3, distinguishes generalized balance and reducible systems. Barge–Diamond (2003) gives a two-letter result with its own scope. Proceed with source completeness for fixed seeds, including the known reducible control, without importing a global R2 average or universal potential.

### Evidence and replay

| Fixed seed (01,10) | Ordered vertices | Child occurrences | Closure |
| --- | ---: | ---: | --- |
| Tribonacci `01,02,0` | 11 | 25 | Work queue drained |
| Reducible non-Pisot control `1,012,1` | 4 | 8 | Work queue drained |

The producer caps are 32 states, 128 child occurrences and 32 inflated letters per track. Lean rebuilds the source from letter/parent/offset triples and independently checks all rows and child closure, including the outgoing rows of coincidences. The hosted workflow compares the full ordered Mojo and Lean packets byte for byte and archives their digests and checkout SHA. Quint independently enumerates both fixed domains and checks the source-bound cycle and parallel edges.

Run `cd kernel && pixi run --locked mojo run -I . tests/test_ordered_occurrence_graph.mojo`. From the repository root, run `npx --yes @informalsystems/quint@0.33.1 test --backend=typescript proof/quint/PscR2OrderedOccurrences.qnt`. The workflow also replays the existing exact rational checker and audits all new Lean declarations.

For a source-bound adversarial score, let `x(e)` be the difference of counts of letter 2 in the two parent prefixes ending at the respective parent indices. Test the residual `(sign(e)−1) x(e)` for comparing child-sign-adjusted and ordinary scores. The actual Tribonacci cycle `2 → 4 → 0 → 2` has residuals `(2,0,0)`; any rational vertex potential would sum to zero. This obstructs that specific score rule on the complete, productive Tribonacci graph.

### Negative controls

Omitted edges, wrong signs, wrong addresses, collapsed parallel edges, and capped outputs are refused. The two occurrences from vertex 4 to vertex 0 begin at offsets 1 and 5 in the inflated tracks. A claimed completion flag cannot make an exhausted replay pass. The original incomplete rational-edge positive control remains separate from the literal cycle obstruction.

### Non-claims / remaining gaps

A child-closed graph for a fixed seed is a finite source domain. The selection of a rational score that is tied to B′ displacement and has the required strict-component density remains open. The Tribonacci obstruction concerns the specified residual on productive data. It supplies neither a strict PIP obstruction nor a PSC closure implication.
