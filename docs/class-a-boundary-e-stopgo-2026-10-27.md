# Stop/go: paired E/H child stars and short physical exits

Proposed scope: complete the actual outgoing stars of E=(x,x,0,0,-1),
H1=(x,y,0,-1,1), H2=(x,y,0,-1,2), and their orientation reversals,
on the entire minus chamber. Certify an at-most-two-step typed coincidence
exit from each of these six packets, retaining every alternative child.

Reused primary-source review: [the current three-source stop/go](class-a-boundary-w-stopgo-2026-10-27.md)
and [the original carrier review](class-a-boundary-child-carrier-2026-10-26.md#targeted-stopgo).
Akiyama--Lee's actual-overlap requirement and every-overlap quantifier,
Barge--Stimac--Williams' overlap/balanced-pair procedure hypotheses, and
Minervino--Thuswaldner's non-unit internal-space obligations remain in force.
This is the same affine one-source calculation and explicit path construction,
not a new spectral mechanism or a proposed global invariant. The literature
reviewed for #355 supplies no all-source or internal-space transfer here.

Decision: proceed with the narrowed six-packet table and exact paths.
Orientation reversal is proved by negating the full offset and swapping the
actual occurrence indices; it is not identification of target packets.
Negative controls include endpoint contact, disjoint actual word pairs,
zero offset with unequal types, invalid free-index clips and corrupted
intermediate transitions. A cycle with an exit remains productive.
BH accepts offset-zero targets at its own scope; this increment checks the
stronger equal-type coincidence terminal and does not reject genuine
zero-offset unequal-type children as geometric edges.

#355 is observed merged at eaff85f1 / merge 316ebdc5, with native run
40474073394 successful. Its new Lean compilation and full Python/TLA jobs
were still queued at this inspection. Merge status is not a proof receipt;
that validation debt is retained and no formal pass is inferred.
