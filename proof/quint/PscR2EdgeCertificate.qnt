// R2C two-edge rational coboundary negative control.
// This abstract graph has a closed directed walk 0→1→0 with
// total edge score 1; no finite rational potential can have these
// weights as exact vertex differences. Not a substitution occurrence.
module PscR2EdgeCertificate {
  var vertex: int
  var cumulative: int

  action init = all {
    vertex' = 0,
    cumulative' = 0,
  }

  action forward = all {
    vertex == 0,
    vertex' = 1,
    cumulative' = cumulative + 1,
  }

  action backward = all {
    vertex == 1,
    vertex' = 0,
    cumulative' = cumulative,
  }

  action step = any { forward, backward }

  val graphVertices = vertex == 0 or vertex == 1
  val nonnegativeTotal = cumulative >= 0

  run positiveClosedCycleTest =
    init.then(forward).then(backward)
      .expect(vertex == 0 and cumulative == 1)
}
