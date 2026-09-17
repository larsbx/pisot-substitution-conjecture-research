# Cross-pollination, round three: the rest of the estate

**Status:** comparative audit dated 2026-09-17, continuing `docs/cross-pollination-round-two-2026-09-16.md`. Round two read seven repositories; this one reads the twelve it never opened. It proves nothing, promotes no claim, and changes no ledger. Status labels follow section 0.2 of the round-one document. Project terms are governed by `claim_governance.toml` here and by `docs/terminology-registry.md` in the Mandelbrot program.

Round two closed with a non-claim: "`coop_substrate` was not read and is not assessed." That was the only repository it named as unread, and the estate turned out to hold eleven more the audit had never listed at all. This document records what is in them.

## 0. What was read

| Tag | Repository | Read | Role |
| --- | --- | --- | --- |
| `CS:` | `larsbx/coop_substrate` | full clone | Elixir signed-event ledger and capital-account substrate, plus the Harness-D evidence pipeline |
| `MT:` | `larsbx/meta_test` | full clone | specification for grading oracle suites as typed, content-addressed verification instruments |
| `NDC:` | `larsbx/native-deployment-control-plane` | README | Elixir deployment control plane on an append-only hash-chained ledger |
| `OW:` | `larsbx/openclaw-workspace` | tree and one document | agent workspace; holds the LLM-to-deterministic refactor roadmap |
| `SP:` | `larsbx/spruce` | README | Elixir/Ash agent platform, the scaffold `sprucegoose` grew from |
| `AI:` | `larsbx/agent-icm` | tree | agent operating layer: policies, workflows, tasks, hooks, skills |
| `IH:` | `larsbx/icm-hub` | tree and one document | numbered knowledge hub mirroring fourteen source areas |
| `BK:` | `larsbx/bizops-kb` | tree | Johnny-Decimal business knowledge base in Obsidian |
| `EB:` | `larsbx/eatsbot` | tree | application carrying the objective-review vocabulary |
| `HQ:`, `ARP:`, `PC:`, `AD:`, `WS:`, `OWG:` | `halaqa`, `agent-runtime-platform`, `pi-cli`, `accountabot_dashboard`, `web-scraper`, `openclaw-workspace-guest` | tree only | classified, not assessed |
| — | `larsbx/cross-pollinated`, `larsbx/finite-mandelbrot-research` | full clone | both empty; see section 4 |

Six repositories were **not read**: `truck-shop`, `redis-pilot`, `nextcloud-calendar`, `listmonk-deploy`, `infisical-deploy`, `vaultwarden-deploy`, and `openclaw-secrets`. They are deployment manifests for third-party services, a category `NDC:` supersedes with its own machinery, and a secrets store that should not be read at all. They are named here so that "not assessed" is a statement rather than a silence.

Markers: `[V]` verified here by reading; `[L]` a claim in the source that this audit did not check.

## 1. The estate states the same six rulings, six times over, and never cites itself `[V]`

This is the finding. Six repositories, written for co-op finance, deployment, oracle grading, agent operations and two mathematics programs, independently arrive at the same small set of rules. No one of them references another for any of it.

### P1. A derived fact is read or generated from its source, never re-derived

`OW: llm-to-deterministic-refactor-roadmap.md` states it as its governing principle: *"If the answer already exists as structured data somewhere in the system, read it. Do not infer it from rendered text, and do not ask a model to re-derive it."* It then names two defect types — regex parsing prose (Type A) and prose instructing a model to enumerate mechanically (Type B) — and fixes each by moving the fact to its structured channel.

That is exactly round-two item R2, which this estate's mathematics side delivered two days later in ignorance of it: one record table, every status surface a function of it. The Mandelbrot program's first generation run found a proof block that gated final acceptance and appeared on no status surface, which is a Type A defect in the roadmap's taxonomy. `CS:` reaches the same place from a third direction: every projection is a pure fold over the log, so a surface cannot disagree with the events.

### P2. A check that cannot fail is not a check

Four statements, four repositories, no shared wording:

| Where | How it is put |
| --- | --- |
| `OW:` roadmap, "Anti-vacuity" | "Every phase carries a regression that fails against current code. A phase whose test passes before the change has not proven anything and is not done." |
| `NDC:` README, restore drill | "The negative control is required evidence; an equality check that never fails is a broken instrument." |
| `NDC:` README, routing check | a deliberately mismatched upstream is run "confirming the check is a working instrument rather than a constant pass" |
| `MT:` INV-4 | "vacuity is uncompilable where provable" — provably vacuous oracles fail to compile, discharged by SMT at DSL compile time |

Round two recorded the same lesson as a correction rather than a rule: R5's first negative control was tautological because the separators were built from the addresses they were meant to separate. The Mandelbrot program has since built a real one. `MT:` is the only place in the estate where the rule is mechanized rather than remembered.

### P3. Inconclusive is a third outcome, never a pass and never a failure

| Where | Name |
| --- | --- |
| `PSC:`, `NLAP:` | a capped run is inconclusive, never a counterexample (UW-2) |
| `FMK: proof_records` | `incomplete`, `bounded` — bounded evidence never closes a general claim |
| `SG:` | `UNEXECUTED`, neither PASS nor FAIL |
| `MT:` A.5 | "Solver `:unknown` MUST be treated as unliftable — never as pass or fail" |
| `OW:` Phase 3 | "Unclassifiable → `ambiguous`, never silently dropped" |
| `CS:` | undeclared constants ⇒ `gate` fails closed |

Six vocabularies for one idea. Round two's A1 noted three of them and proposed mapping them onto each other; the map `FMK: proof_records/vocabularies.py` now holds covers two.

### P4. A derived or machine-produced artifact never authorizes

`CS:` is the sharpest: `MachineExtractionRecorded` is *"a proposal carrying the raw-artifact hash, never authoritative; promotion = human `FindingExtracted`; demotion = `CorrectionRecorded`."* `MT: INV-3` says of its own judge suite: *"measured always, trusted never."* `SG:` separates four authority planes so that a projection never authorizes. `FMK: proof_records` refuses to let a bounded experiment close a general claim. `NDC:` binds every call to one resource and one declared action and refuses anything else.

### P5. Make the illegal state unrepresentable, not merely rejected

`CS:`: *"`BuildStarted(D)` without `gate(D)` unrepresentable"*; an unversioned instrument edit is impossible because the version is content-addressed. `SP:`: *"there is no path to `:acting` that bypasses `:thinking`, even if the GenServer crashes mid-turn."* `NLAP:` enforces its membership lifecycle at the append gate rather than in a checker downstream. `MT: INV-3` makes the shown/judge partition verifier-enforced at compile time.

The research repositories are one rung below this. They reject bad states at the boundary and say so loudly, which is weaker than not being able to build one.

### P6. Fail-closed has a direction, and only one repository says so

`NDC:` alone states it: *"For deploy gates, failing closed means refusing to proceed. For a destructive operation, failing closed means refusing to **delete**. Uncertainty is never resolved in favour of deletion."* Everywhere else in the estate, including both mathematics programs, "fail closed" is used as though it had one meaning. It has two, and they point opposite ways.

## 2. What each repository holds that the research programs do not

### C1. `MT:` grades the oracle, which is the layer both programs are missing `[V]`

`MT:` studies *the oracle suite, not the implementation under test*, and asks "does this suite constrain anything, and how much?" Three instruments: typed non-vacuity (uncompilable vacuous oracles), empirical discrimination (kill-rate over a labelled population of fault-seeded implementations), adversarial gating (held-out mutation operators as feasibility constraints).

Its oracle taxonomy is the research programs' testing practice, named:

| `MT:` family | Instance here |
| --- | --- |
| known-answer | the pinned constants of every Mojo smoke target |
| property | `FMK: tools/property_oracle.py`, the exact-arithmetic probe |
| metamorphic | `PSC:` relabelling and reversal normal forms |
| reference (differential) | every `tools/*_reference.py` in `NLAP:`, the Python oracle layer of `PSC:` |
| model-based | the TLA+ layer, which `MT:` would derive rather than author |

The sharpest transfer is `MT:`'s requirement that a generator declare a **codomain refinement `φ_G`** — the input distribution is a declared, checked object rather than an accident of how the test was written. Round two recorded, in its own words, the failure that requirement exists to prevent: the M-adic carrier's soundness defect survived differential testing because "every coordinate it generated lay in `[-9, 9]`, where the wrap is unreachable", and the audit generalized it to "a differential test is only as strong as its input distribution". `MT:` is the mechanism for the moral the audit drew. `[L]` on `MT:`'s own claims: the specification is normative and unimplemented, and says so — S0 is blocked and implementation is not authorized.

### C2. `CS:` is a fourth content-addressed evidence ledger, and the only one with two implementations of its codec `[V]`

Round two's A1 compared three: `SG:`'s `ContentID`, `FMK:`'s length-prefixed records, `CC:`'s manifest. `CS:` is a fourth, and its opportunity-1 problem is already solved inside it: `CoopEventCanonicalV1` is a frozen strict-CBOR profile **implemented twice** — a Rust NIF for production and a pure-Elixir reference for test — and locked with committed byte-level vectors that both must reproduce. A1 proposed cross-testing `SG:`'s canonical encoding against `FMK:`'s golden vectors; `CS:` shows what the finished form looks like, and adds a boot gate: the application refuses to start if it cannot reproduce its known-answer vectors.

Two further pieces the research side lacks: **as-of reads** (`gate` is "as-of reproducible"; `PSC:`'s ledger has no notion of what it said last week) and **in-log rule versioning applied forward-only**, which is what a proof-record ledger would need before it could restate its own history.

### C3. `NDC:` runs a reproducible-build gate that is a proof record in production `[V]`

`NativeDeployment.BuildManifest` requires every build input to be declared — exact source commit, immutable builder image digest, ordered commands, environment values, content-addressed input paths — encodes them canonically, and derives a SHA-256 identity. Repeating a build with different output fails closed as `:non_reproducible_build`.

That is `FMK:`'s `verified_finite_computation` record, whose required evidence is exactly `replay` and `digest`, built for deployments instead of censuses. `PSC:`'s census records name a replay command and a digest; `NDC:` enforces that re-running it reproduces the artifact. The research side asserts replayability; `NDC:` checks it.

`NDC:` also supplies P6 above, and one structural idea neither mathematics program has: `assert_reclaimable/4` refuses to judge a preview in isolation because per-project minimum retention *"is a property of the whole set"*. That is the same shape as the separated-pair density correction, where flattening the endpoints into one cut set counted atoms that are not separated from each other as though they were — a class property misread as an element property. Two repositories, two domains, one error, both caught.

### C4. `OW:` has written the estate's methodology down, and the research repositories have not read it `[V]`

Besides P1 and P2, the roadmap draws a boundary the research programs draw informally: it lists what must *not* be mechanized — "Audit / observer / decider judgement roles", approval that "stays deferred and read-only" — and says converting them to rules "would be the same category error in the opposite direction". `PSC: AGENTS.md` makes the same split between exploratory search and certificate, without ever saying why the split exists.

### C5. `EB:` shows the objective-review vocabulary already has a non-research consumer `[V]`

`EB:` carries `OBJECTIVE_REVIEW_REPORT.md`, `UNIVERSAL_CRITIQUE.md`, `UNIVERSAL_ACTION_PLAN.md` and `STANDARDS.md`. Round-two item R6 delivered the Research Hygiene Manifesto into `ORM:` with `claim_governance` as its reference implementation; `EB:` is evidence that the review vocabulary travels to ordinary applications, which is the readership R6's manifesto was written for.

### C6. Two documentation taxonomies, no bridge `[V]`

`BK:` uses Johnny-Decimal (`00-09 System-management area`, `10-19 …`), `IH:` uses a numbered hub (`01-openclaw` … `14-copyparty`), and `MT:` files its documents under `docs/65-roadmaps/` and `docs/66-workflows/`, citing a "canonical Systemwide SOP taxonomy". The research repositories use a flat `docs/` with long dated filenames. Neither convention is better; the point is that `MT:`'s roadmap and `PSC:`'s ledger index are the same kind of object filed two different ways, so nothing can walk both.

## 3. Ranked next contributions

| Rank | Contribution | Repositories | Kind | First file |
| --- | --- | --- | --- | --- |
| R9 | Declare the input distribution of every differential oracle, per `MT:`'s `φ_G`, starting with the two that hid a soundness defect | FMK, PSC, NLAP | tooling, mathematics | `FMK: tools/property_oracle.py`; `NLAP: tools/*_reference.py` |
| R10 | Cross-test `CS: CoopEventCanonicalV1` against `FMK: fixtures/vectors.json`, and adopt its boot-gated known-answer self-test | FMK, CS | infrastructure | `FMK: tests/proof_records/test_vectors.py` |
| R11 | Mechanize the property-to-test tables: `CS: HARNESS.md` P1–P8 and `NDC:`'s acceptance list are prose; the `coverage` check of R8 already does this for a claim ledger | CS, NDC, FMK | tooling | `FMK: audit/claim_governance/checks/coverage.py` |
| R12 | Write P1–P6 once, as operational rulings beside the Research Hygiene Manifesto, each citing the repositories that state it | ORM, all | documentation | `ORM:` manifesto directory |
| R13 | Give fail-closed a direction in both mathematics programs' vocabularies, per `NDC:` | PSC, NLAP | documentation | `PSC: AGENTS.md`; `NLAP: docs/` |
| R14 | Resolve the two empty repositories of section 4 | — | governance | — |
| R15 | Import `CS:`'s as-of reads and forward-only in-log rule versioning into the proof-record model, so a ledger can restate its own history | FMK | infrastructure | `FMK: docs/proof-records-specification.md` |

R9 is first because it is the only item that answers a defect the estate has already suffered rather than one it might. R10 is second because the encoding convergence was round two's cheapest item and `CS:` has since finished the hard half of it.

## 4. Two empty repositories, one of them a name collision `[V]`

- `larsbx/finite-mandelbrot-research` was created on 2026-09-17 and contains one file: a README holding its own title. The live program is `larsbx/finite-mandlebrot-research`, spelled with the transposition, and carries the whole Mandelbrot repository. Anyone or anything resolving the correctly spelled name reaches the empty one. `FMK: README.md` and both cross-pollination audits cite the misspelled name as canonical, so the live name is the one with the typo in it.
- `larsbx/cross-pollinated` is likewise a single README holding its title. Nothing in either audit refers to it.

Neither is a mathematical matter. Both are recorded because a reader who searches the estate by name will find them first.

## 5. Non-claims

- Nothing here bears on `OverlapProductivity`, `ResidualClosureNoMissingLinks`, `C1`, or any conjecture status.
- Section 1 is a claim about wording and structure in documents, not about the correctness of any repository's code. Where a repository states a property of itself, this audit records the statement and marks it `[L]` if it did not check it.
- `MT:`'s three instruments are a specification, not a running system: its own README says implementation is not authorized and S0 is blocked. Nothing here treats its guarantees as available.
- The six repositories listed as not read in section 0 are not assessed, and their absence from section 1 is not evidence that they lack the rulings.
- `coop_substrate`'s charter constants are flagged in its own source as placeholders awaiting declaration; no number taken from it is a real value, and none is used here.
