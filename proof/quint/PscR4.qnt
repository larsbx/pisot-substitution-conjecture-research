// R4 adversarial control: bounded overlap offset and a stable
// finite window do not force a zero offset, even under repeated inflation.
module PscR4OverlapWindows {
  var offset: int
  var overlapAge: int
  var commonTileSeen: bool

  action init = all {
    offset' = 1,
    overlapAge' = 0,
    commonTileSeen' = false,
  }

  // Nonzero periodic affine overlap: x -> 2x - 1.
  action forcedOverlap = all {
    offset == 1,
    offset' = 2 * offset - 1,
    overlapAge' = overlapAge + 1,
    commonTileSeen' = commonTileSeen,
  }

  // Zero offset is only a common-vertex candidate, not by itself a
  // common tile; an independent label/occurrence match is needed.
  action zeroOffsetCandidate = all {
    offset == 0,
    offset' = 0,
    overlapAge' = overlapAge + 1,
    commonTileSeen' = commonTileSeen,
  }

  action step = any { forcedOverlap, zeroOffsetCandidate }

  val finiteOffsetBox = offset >= -2 and offset <= 2
  val noUnjustifiedCoincidence = not commonTileSeen
}
