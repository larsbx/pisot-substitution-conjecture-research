# Exact arithmetic binding (PSC)

**Status:** this repository's binding table for the rational and interval arithmetic specification, `larsbx/finite_exact:docs/rational-interval-arithmetic-spec.md` (sections 0 to 5, repository-independent; section 6 asks each consumer to keep exactly this table). It states no theorem: exactness removes one class of error, and the epistemic status of every computation is governed by `verification-architecture.md` and the claim-status documents.

Classes: CONFORMS (criteria C1 to C7 with an unbounded backend), CONFORMS-CHECKED, DEMO, QUARANTINED, as defined in the specification.

| Spec item | Module | Class | Notes |
| --- | --- | --- | --- |
| 1.1 integer backend, 1.1–1.3 ℚ | `mojo/finite_exact/bigint_z.mojo`, `mojo/finite_exact/rat_q.mojo` | CONFORMS | vendored byte-for-byte from `larsbx/finite_exact` at the commit pinned in `vendored.toml`; `scripts/check_vendored_sync.py` compares SHA-256 digests, so any local edit fails CI |
| 2.1–2.5 I_Q and rank-2 boxes | `mojo/interval_q/closed_q.mojo` | CONFORMS | vendored from `larsbx/interval_q`, same pin discipline |
| PSC conventions over the packages | `mojo/psc/exact.mojo` | CONFORMS | a rejected enclosure raises, a rejected scalar in integer-seeded polynomial arithmetic aborts as an impossible state; Horner helpers, midpoint, diagnostic rendering; integer lifts re-exported from `finite_linear_algebra.scalar` |
| 1–2 direct consumers | `mojo/finite_linear_algebra/{scalar,qlinalg,tensor3,w3}.mojo` (vendored from `larsbx/finite_linear_algebra`), `mojo/psc/pisot.mojo`, `mojo/psc/real_root_sign.mojo` | CONFORMS | exact linear algebra, Sturm sequences, and the PIP screen over unbounded rationals; the former machine-width `Rat` and `CheckedRat` are deleted |
| 2.3 enclosure of `β ∉ ℚ` | `mojo/psc/perron_interval.mojo` (`perron_root_interval`) | CONFORMS | integer bracket by exact sign changes, then bisection with unbounded endpoints |
| 3.2 filter-then-exact | `mojo/psc/perron_interval.mojo` (`perron_sign_decision`) with oracle `psc.perron_field3.sign_at_perron` | CONFORMS | R1: fallback on `0`; R2: `interval_certified` flag |
| 3.3 skeleton/margin split | `mojo/psc/overlap_interval_audit.mojo`, `mojo/psc/overlap_contracting.mojo` | CONFORMS | overlap graph exact; margins interval-first with exact fallback; uniform minimum reported only when every margin is interval-certified |

Hook (specification section 7, consumer side): the vendoring pin in `vendored.toml` checked in CI and by `scripts/verify_all.sh`; the law and smoke checks of the packages re-run under the PSC toolchain by `mojo/tests/test_finite_exact.mojo`; the PSC-specific interval tests in `mojo/tests/test_exact_interval.mojo` (natural Horner extension containment, division across zero fails closed, Perron-root enclosure), which are the first external consumer test named by the `interval_q` package. PSC has no floating-point audit script of its own; `audit-2026-09-15.md` records that no `Float32`/`Float64` appears under `mojo/psc/`.
