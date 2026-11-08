// Quantitative refinement of the source-complete rank certificate.
// Import only pure source definitions; do not import another module's runs
// or state variables and accidentally inflate the named-test inventory.
module PscR1RankWitness {
  import PscR1SupportCertificate.rankCheck from "./PscR1SupportCertificate"
  import PscR1SupportCertificate.target from "./PscR1SupportCertificate"
  import PscR1SupportCertificate.fibImages from "./PscR1SupportCertificate"
  import PscR1SupportCertificate.fibPairs from "./PscR1SupportCertificate"
  import PscR1SupportCertificate.fibRows from "./PscR1SupportCertificate"
  import PscR1SupportCertificate.fibRank from "./PscR1SupportCertificate"
  import PscR1SupportCertificate.binaryImages from "./PscR1SupportCertificate"
  import PscR1SupportCertificate.binaryPairs from "./PscR1SupportCertificate"
  import PscR1SupportCertificate.binaryRows from "./PscR1SupportCertificate"

  // Validate the source-complete certificate before looking up any row.
  // The first decreasing child in LITERAL ORDER is chosen deterministically.
  // Stops extending a witness after a genuine source-defined diagonal.
  pure def witness(images, pairs, rows, rank, start) =
    if (not(rankCheck(images,pairs,rows,rank)) or start < 0 or start >= pairs.length()) List()
    else range(0, rank[start]).foldl(List(start), (path, _) => {
      val s = path[path.length() - 1]
      if (target(pairs[s])) path else {
        val lower = rows[s].select(t => rank[t] < rank[s])
        if (lower.length() == 0) path else path.append(lower[0])
      }
    })

  // Independently replay a purported bounded path; even a rank certificate
  // cannot authorize an invented edge, a different root or a false target.
  pure def validWitness(images, pairs, rows, rank, start, path) =
    if (not(rankCheck(images,pairs,rows,rank)) or start < 0 or start >= pairs.length()) false
    else if (path.length() == 0 or not(path.indices().forall(i =>
      path[i] >= 0 and path[i] < pairs.length()))) false
    else path[0] == start and path.length() - 1 <= rank[start] and
      target(pairs[path[path.length() - 1]]) and
      range(0, path.length() - 1).indices().forall(k =>
        rows[path[k]].indices().exists(j => rows[path[k]][j] == path[k+1]) and
        rank[path[k+1]] < rank[path[k]])

  pure val binaryEqualRanks = List(1,1,1,0,0)
  var active: bool
  action init = active' = true

  run concreteBoundedWitnessTest = init.expect(all {
    active,
    witness(fibImages,fibPairs,fibRows,fibRank,0) == List(0,2),
    witness(fibImages,fibPairs,fibRows,fibRank,1) == List(1,2),
  })
  run everyCoveredStateHasBoundedWitnessTest = init.expect(all {
    active,
    fibPairs.indices().forall(s => validWitness(fibImages,fibPairs,fibRows,fibRank,s,
      witness(fibImages,fibPairs,fibRows,fibRank,s))),
  })
  run initialTargetNeedsZeroStepsTest = init.expect(all {
    active,
    witness(fibImages,fibPairs,fibRows,fibRank,2) == List(2),
    witness(fibImages,fibPairs,fibRows,fibRank,3) == List(3),
  })
  run equalityIsNotRankProgressTest = init.expect(all {
    active,
    not(rankCheck(binaryImages,binaryPairs,binaryRows,binaryEqualRanks)),
    witness(binaryImages,binaryPairs,binaryRows,binaryEqualRanks,1) == List(),
  })
  // A longer actual target path exists, but it is not a witness within
  // rank(start)=1. The certificate promises SOME bounded path, not all.
  run longerActualPathNotBoundedWitnessTest = init.expect(all {
    active,
    not(validWitness(fibImages,fibPairs,fibRows,fibRank,0,List(0,1,2))),
  })
  run fabricatedTargetEdgeRejectedTest = init.expect(all {
    active,
    target(fibPairs[3]),
    not(validWitness(fibImages,fibPairs,fibRows,fibRank,0,List(0,3))),
  })
  run nontargetEndpointRejectedTest = init.expect(all {
    active,
    not(validWitness(fibImages,fibPairs,fibRows,fibRank,0,List(0))),
  })
  run differentSourceRootRejectedTest = init.expect(all {
    active,
    not(validWitness(fibImages,fibPairs,fibRows,fibRank,0,List(1,2))),
  })
  run malformedTraceRejectedTest = init.expect(all {
    active,
    not(validWitness(fibImages,fibPairs,fibRows,fibRank,0,List())),
    not(validWitness(fibImages,fibPairs,fibRows,fibRank,0,List(0,99))),
    not(validWitness(fibImages,fibPairs,fibRows,fibRank,0,List(0,-1))),
    witness(fibImages,fibPairs,fibRows,fibRank,99) == List(),
  })
}
