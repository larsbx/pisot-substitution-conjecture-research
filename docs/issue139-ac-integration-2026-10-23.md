# Reconcile PR #326 with merged PR #327

This is an integration repair, not a new mathematical promotion. Merge main
`2bfb350` into #326 head `ed51df0`, preserving both exact certificate packets.
Main's #327 and #326 independently generated different valid class-A gap-four
ranks and occurrences. A textual union of their table rows is not a certificate.

## Resolution

- Keep main's `class_a_ray_d4p.mojo`, `class_a_ray_d4m.mojo`, default registry,
  `ALine` domain correction, complete-prefix test and finite helper limit 48.
  The typed-carrier budget refusal is updated to 49.
- Preserve #326's two table files byte-for-byte as `class_a_ray_d4p_rank.mojo`
  and `class_a_ray_d4m_rank.mojo`, with a dedicated eight-ray registry and test.
  Both versions use the same exact closure/descent checkers. There is no
  duplicate implementation of the proof mechanism.
- The default plus r=3 certificate starts at n=15; #326's alternative starts
  at n=19. On minus r=0,1 the alternative bound l+4 improves on main's
  2l+9 and 2l+7. Keep these as separate verified certificates with their
  own floors, occurrence choices and bounds.
- The failed finite-fit regression reads the alternative tables, whose pieces
  and occurrences it compares. It must not silently bind to main's different
  valid tables. Rank synthesis selects these files explicitly with
  `--rank-tables`; its default continues to use the standard registry files.
- Retain the class-C certificate and its sources unchanged. Both evidence
  packets and their SHA256SUMS stay byte-identical. Preserve both side-note
  histories, then regenerate the proof bank from the combined documents.

The original #326 packet replays its archived A receipt at `ed51df0`; #327's
packet belongs to its own recorded source revision. On the integrated tree,
run `test_class_a_residue_rays.mojo` for the standard 18 rays and
`test_class_a_gap_four_rank.mojo` for the eight alternative certificates.
`test_class_c_gap_four.mojo` remains the C replay. The Python
`tests/test_issue139_gap_four.py` checks the alternative counts against all
eight original exact verdicts and retains the failed-rank control.

## Proof-bank review repair

The review of #326 correctly found that the generated C4 locator pointed at
proof prose. The statement scanner must count newlines in the same masked
text whose match offsets it uses. This preserves source line numbers when a
fenced block is replaced with newline placeholders. A fenced-block regression
and exact C4 locator check guard the repair; both generated outputs are rebuilt.

## Validation and scope

Fresh integration receipts are in
`evidence/issue139-ac-integration-2026-10-23/`. Historical native receipts are
not relabelled as integrated-tree runs. Required hosted CI remains separate.
Both A/C gap-four theorems retain their scope. A/C gaps d>=5, universal #139,
#138/#84, G1 and PSC remain open; independent human review remains pending.
