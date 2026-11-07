// R3 adversarial control: bounded zero-return gaps do not imply
// diagonal letter coincidences; a nonproductive reset cycle survives.
module PscR3PrefixReturns {
  var sinceCut: int
  var discrepancy: int
  var cuts: int
  var coincidenceSeen: bool

  action init = all {
    sinceCut' = 0,
    discrepancy' = 0,
    cuts' = 0,
    coincidenceSeen' = false,
  }

  action topLetter = all {
    sinceCut < 2,
    sinceCut' = sinceCut + 1,
    discrepancy' = discrepancy + 1,
    cuts' = cuts,
    coincidenceSeen' = coincidenceSeen,
  }

  action bottomLetter = all {
    sinceCut < 2,
    sinceCut' = sinceCut + 1,
    discrepancy' = discrepancy - 1,
    cuts' = cuts,
    coincidenceSeen' = coincidenceSeen,
  }

  action balancedReset = all {
    sinceCut > 0,
    discrepancy == 0,
    sinceCut' = 0,
    discrepancy' = 0,
    cuts' = cuts + 1,
    coincidenceSeen' = coincidenceSeen,
  }

  action step = any { topLetter, bottomLetter, balancedReset }

  val withinBound = sinceCut >= 0 and sinceCut <= 2
    and discrepancy <= sinceCut and -discrepancy <= sinceCut
}
