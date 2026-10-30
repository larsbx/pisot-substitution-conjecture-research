# Branch and conjugate audit of the open boundary stacks (2026-10-30)

Status: provenance/governance audit. No theorem, claim status, kernel or
archived receipt changes. Every check below compares records or runs the
existing independent oracles; nothing here is new mathematical evidence.

## Scope

All 306 remote branches at `main` 59ee391b, with full history
(the session clone was shallow and was unshallowed first). Here a "conjugate"
is a second record of one object under a different branch, name or
orientation:

* the same packet carried by several branches;
* the same specimen under two names;
* a specimen whose actual reversal `R(a,b,p,q,r)=(b,a,-p,-q,-r)` was
  certified elsewhere.

## Method

1. **Branch state.** For each branch: is it an ancestor of `main`? If not,
   is every file it changes present in `main` history, either as a blob or
   (for shared append-only files) as the same added lines?
2. **Packet duplication.** For every `evidence/<packet>/` that has not landed,
   list the branches that carry it and compare their tree hashes.
3. **Topology.** Build the ancestry DAG of the branches that have not landed.
   Test content containment and `git merge-tree` conflicts between the tips
   and `main`.
4. **Specimen conjugates.** Match exact tuples, and their reversals, across
   the docs of `main`, the live class-A tip and the T/X/Y0 tip. Compare the
   claims by running the independent oracles. The shared
   `oracles/python/class_a_boundary_children.py` has one blob on every
   line compared, `ed0e7312`.

## Findings

### Branch state

* 156 branches are ancestors of `main`.
* 69 more have all of their content in `main` history, so nothing in them
  is lost.
* 81 branches still carry content that has not landed.

The remaining duplicated packets show no divergence: every packet held by
several branches is byte-identical across them.

### Live stacks

```
class A (main line)  main <- p3-10-28 (#372) <- q3 (#373) <- b3 <- b4 (#377) <- r4 (#378)
                     <- b5 <- y4 (#379) <- j8 <- e6 (#382) <- p9 <- j9 (#391) <- w9 <- h9 (#395)  TIP
class A (side)       y4 <- d5 <- r5 (#380)                                                     TIP
class A (older)      main <- p3-10-27 (#366) <- tx (#371)                                      TIP
class C              main <- slope-three (#392) <- below-three (#394)                          TIP
                     main <- descendant-wall (#406) <- r-transfer (#408)                       TIP
```

* `r3` adds nothing beyond `b4`.
* `d0` is contained in `e6` through #387; see the #386 closure entry in the
  ledger.
* Each tip conflicts with `main` only in `docs/side-notes-ledger.md`, and
  `h9` and `r5` conflict with each other only there too.
* #392 and #394 stack, but both PRs target `main`, so #394's diff shows
  #392's work as well. The same holds for #406 and #408.

### Competing P3 lines (#366/#371 vs #372)

`p3-10-27` and `p3-10-28` each write the same five P3 kernel, oracle and
test files and the P3 workflow, with real content conflicts. Replaying both
P3 oracles over 117 members gives:

| | #366 (p3-10-27) | #372 (p3-10-28) |
| --- | --- | --- |
| stars | P3, R(P3) | P3, T=(y,x,0,-1,1), U=(x,x,0,-1,1), and reversals |
| accepted / pairs | 5,382 / 122,616 | 17,316 / 542,880 |
| outgoing union | 26 labels | 37 labels |
| P3 exit | <=4 edges (2 at n>=4) | <=2 edges at every n |

The P3 star is identical in both (2n-3 children at every member). #366's
26 labels are exactly the P3 star union and lie inside #372's 37. So #372
subsumes #366's P3 result.

### Specimen conjugates under different names

| Tuple | Names in use | Agreement |
| --- | --- | --- |
| (x,y,1,-1,1) | `T` in #371; `Q3` in #373 | both claim one child (A+1,0)->X; stars agree on 117/117 members |
| (y,y,1,-1,-1) | `Y0` in #371 | equals R(T_1) for main's minus `T_1=(y,y,-1,1,1)`, whose star has been on `main` since 2026-10-26; Y0's star equals the reversed T_1 star on 117/117 members, with identical word systems |
| (x,x,1,0,-1) | `X` | one canonical star on `main`; #371 and #373 reuse it |
| (y,x,0,-1,1) | `Q` on `main` (W path); `T` from #372 on; `V`/`V1` in the U internal-hit line | one specimen with three names. On `main`, `V` is the different (y,x,0,-1,2) |

So among #371's six oriented stars, T and Y0 (and their reversals)
re-derive stars recorded elsewhere, and X is reused. What #371 adds that is
not recorded elsewhere: its 42-label T/X/Y0 union, Y0's selected exit
Y0(t+1,1)->(y,y,0,-2,3)->(y,x,0,1,-1)->C, and the t=0 last-c controls.

### Orphaned shorter U exit (#354)

The four-edge internal coincidence

seed `(x,c,0)` -(1,2)-> `T_1` -(0,t+1)-> `U=(x,y,1,2,-3)` -(d+3,0)-> `(y,x,0,-1,1)` -(1,2)-> `C`

was merged as #354 into the old `research/class-a-boundary-u-2026-10-26`
branch after that branch's PR #352 had closed. It has never reached `main`
or the live stack. `main` records only the six-step W seed path. Using
`main`'s Geometry, `U(d+3,0)->(y,x,0,-1,1)` and `(y,x,0,-1,1)(1,2)->C`
both hold on all 117 members. This is a finite replay of an existing
record, not a new universal claim; #354's own derivation carries the
quantifiers.

## Replay

```
git fetch --unshallow origin
python3 -I oracles/python/class_a_boundary_p3_children.py   # on each P3 line; compare image_labels, accepted
```

The conjugate star comparisons call `Geometry(-1,k,t).edges(w)` for k<=12
and t<=8 from `oracles/python/class_a_boundary_children.py`. Each compares
`edges(w)` with `{(j,i,R(x)) : (i,j,x) in edges(R(w))}`, and compares
#371's `predicted` against #373's Q3 table.

## Non-claims

* No PR or branch has been closed, retargeted or deleted. Retiring #366/#371
  as superseded is a decision for the maintainer, as is importing #354's
  four-edge exit.
* Equal stars do not make two records interchangeable as certificates.
  Each keeps its own scope, receipts and review status.
* Independent human review remains pending for every packet named here.
