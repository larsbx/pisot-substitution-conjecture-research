# Stop/go: occurrence-indexed X-descendant productivity

Proposed experiment: complete the strict minus-class-A overlap graphs from
all 18 genuinely oriented swap sources, retain every indexed edge, audit
SCCs and reverse coincidence reachability, and seek typed transfer/escape
rules for X descendants. Parameters are integers k,t>=0; offsets are full
bottom-minus-top Parikh vectors. No parameter extrapolation from samples.

Primary sources inspected before writing the diagnostic:

* Akiyama--Lee, *Algorithm for determining pure pointedness of self-affine
  tilings*, https://arxiv.org/pdf/1003.2898: the established construction is
  an overlap graph and reachability to coincidence, with actual/potential
  overlap and realization hypotheses. Graph reachability is standard, not
  a new theorem here. A swap-seeded graph is not automatically that entire
  realized overlap graph.
* Akiyama, *Strong coincidence and overlap coincidence*,
  https://arxiv.org/pdf/1509.04471: the converse requires coincidences for
  sufficiently many choices of control vertices. A selected seed path
  cannot replace all-descendant productivity or those hypotheses.
* Mercat--Akiyama, *Yet another characterization of the Pisot substitution
  conjecture*, https://arxiv.org/pdf/1810.03500: the automata criterion is
  stated for irreducible **unit** Pisot substitutions. This chamber has
  incidence determinant -2, so that criterion does not directly transfer.

Read main's append-only side-notes ledger, especially the realized recurrent
loop/good-exit controls and class-A finite-carrier nontransfer findings.
Reversal covariance and forward closure alone do not force productivity;
an indefinitely traversable cycle can still have an existential good exit.
Typed coincidence requires equal letters AND all three offset coordinates
zero. Endpoints and true FIRST/RUN/LAST occurrences must be retained.

Decision: **proceed with the narrowed exact finite audit and local symbolic
transfer certificates**. Do not import a spectral theorem, identify nine
orientations with eighteen, infer unbounded parameter behavior from a table,
or reuse a translated star without rechecking strict clipping. PRs
#428/#430/#431/#432/#433 remain unmerged with exact-head CI pending at the
start of this work. Their universal closure reduction is provisional.

Initial implementation constraint: this environment had neither Mojo nor
pixi on PATH and a filesystem search found neither executable. Python was
used for exploratory work under AGENTS.md while bootstrapping the toolchain.
The initial Pixi installer failed on archive ownership; extracting with
`--no-same-owner` resolved that environmental issue. The locked toolchain
then installed successfully: Mojo 1.1.0.dev2026090805. **The blocker is now
resolved.** Native indexed-graph and ladder modules and regressions accompany
the independent Python oracle; no Python-only implementation exception is
being requested for the final contribution. Native tests and the oracle
remain finite evidence, not a canonical universal SCC certificate.
