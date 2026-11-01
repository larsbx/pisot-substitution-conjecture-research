# PR #439 native-normalization acceptance repair, 2026-10-31

Status: local repaired-source acceptance recorded; hosted exact-head CI and
ordered integration after #438 remain pending. This packet does not replace
any original pending receipt or represent independent human review.

The exact native constructor was inspected in `psc.perron_field3`:
`_row_entry` transposes the incidence matrix and subtracts beta on its
diagonal; the first nonzero cross product is selected, oriented positively,
and verified as a left eigenvector. For the stated literal class-A words the
first row pair yields Nx=A(beta-1), Nc=d-n+n*beta, Ny=(beta-1)(beta-2).

For n=k+t+3,d=k+2t+5, chi(n+2)=(n-d-1)(n+2)+2<0, so its largest real root
beta exceeds n+2>=5. All three native lengths and gamma=(beta-2)/beta are
strictly positive. Reducing beta*gamma modulo chi gives beta-2 exactly;
the independent Python tests verify gamma*Li=Ni coefficientwise.

The native coefficient matrix is [[-A,d-n,2],[A,n,-3],[0,0,1]]. Expanding its
determinant gives -A*n-A*(d-n)=-A*d. Summing the encoded coefficients gives
d*q; the second coefficient plus 3*w-n*q gives A*p. Hence the two guards
are necessary; substitution of the decoded coordinates proves sufficiency.
The native assertions include a shift failing only the second guard.

`selected_overlap_child` uses beta*shift+bottom_prefix-top_prefix and reads
the literal indexed letters. The adapter independently counts those same
proper prefixes, applies full incidence, compares the entire typed native
state, decodes its shift and checks strict parent/child overlap. The parent
helper in #438 alone does not certify literal occurrence existence.

Replay from the root (Pixi on PATH):

```sh
python -m pytest -q tests/test_class_a_parikh_field_bridge.py tests/test_class_a_native_normalization.py tests/test_markdown_links.py
PYTHONPATH=tools python -m claim_governance.cli --root . --check coverage
PYTHONPATH=tools python -m claim_governance.cli --root .
(cd kernel && pixi run --locked mojo run -I . tests/test_class_a_parikh_field_bridge.mojo)
(cd kernel && pixi run --locked mojo run -I . tests/test_class_a_native_length_contract.mojo)
```

Logs record 12 Python tests (nine exact-arithmetic tests plus three link
regressions), full governance and both native test receipts (6,125 parent
cases, 2,500 native cases). The JSON manifest binds sources and lockfile.
The focused hosted workflow checks out the exact PR head, requires the
post-assertion receipts and uploads the tested revision and source hashes.
No repository-wide suite receipt is fabricated by this targeted run.

The new invalid-occurrence controls include negative/out-of-range indices
and a genuine occurrence choice whose child fails strict overlap. The
wrong-scale/order and both off-lattice controls remain in place. These
are finite implementation checks of the documented normalization identities,
not complete descendant coverage, all-parameter productivity, BH or PSC.
