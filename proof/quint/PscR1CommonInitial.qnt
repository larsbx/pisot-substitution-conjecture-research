// The correct positive certificate for the ACTUAL Tribonacci source.
// All three letter images begin in 0. Lean proves the lifting to every
// nonempty word pair; these tests independently check its finite premise.
module PscR1TribonacciAllStatePrefix {
  pure val images = List(List(0,1), List(0,2), List(0))
  pure def inflate(w) = w.foldl(List(), (out,a) => out.concat(images[a]))
  var active: bool
  action init = active' = true
  run allLetterImagesStartZeroTest = init.expect(all {
    active,
    images.indices().forall(a => images[a].length() > 0 and images[a][0] == 0),
  })
  run allNineOrderedLetterPairsTest = init.expect(all {
    active,
    images.indices().forall(a => images.indices().forall(b =>
      images[a][0] == images[b][0])),
    inflate(List(0,1)) == List(0,1,0,2),
    inflate(List(1,0)) == List(0,2,0,1),
  })
  run binaryMixedBranchPremiseRejectedTest = init.expect(all {
    active,
    List(0,1)[0] != List(1,0)[0],
  })
}
