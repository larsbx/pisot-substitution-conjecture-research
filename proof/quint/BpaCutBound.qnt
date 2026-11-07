// Bounded ONE-COORDINATE local discrepancy within a balanced block.
// Explicit finite bound L = 3. A common cut is allowed only if diff = 0.
// This is a finite-state control, not a proof that arbitrary BPA descends
// from substituted prefix pairs or that spectral conjugates contract.
module BpaCutBound {
  var gap: int
  var diff: int

  action init = all {
    gap' = 0,
    diff' = 0,
  }

  action plus = all {
    gap < 3,
    gap' = gap + 1,
    diff' = diff + 1,
  }

  action minus = all {
    gap < 3,
    gap' = gap + 1,
    diff' = diff - 1,
  }

  action same = all {
    gap < 3,
    gap' = gap + 1,
    diff' = diff,
  }

  action balancedCut = all {
    gap > 0,
    diff == 0,
    gap' = 0,
    diff' = 0,
  }

  action step = any { plus, minus, same, balancedCut }

  val cutBound = gap >= 0 and gap <= 3 and diff <= gap and -diff <= gap
}
