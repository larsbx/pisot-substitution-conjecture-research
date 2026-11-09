// Historical negative diagnostic; NOT part of the accepted formal model.
// The nested helper formulation produced [0,0] for a mathematical deficit
// [0,2] under both Quint 0.33.1 backends in this environment.
// Direct folds in proof/quint/PhysicalMass.qnt avoid this formulation.
// Preserve this reproduction; do not infer an upstream defect diagnosis.
module PhysicalMassHelperReproducer {
  pure def mapList(xs, f) = xs.foldl(List(), (out, x) => out.append(f(x)))
  pure def transposeMultiply(t, h) = range(0, t.length()).mapList(j =>
    0.to(t.length() - 1).fold(0, (sum, i) => sum + t[i][j] * h[i]))
  pure def deficit(t, h, theta) = {
    val columns = transposeMultiply(t, h)
    range(0, t.length()).mapList(j => theta * h[j] - columns[j])
  }
  var result: List[int]
  action init = result' = deficit(List(List(2, 0), List(0, 0)), List(1, 1), 2)
  run mathematicallyExpectedResultTest = init.expect(result == List(0, 2))
}
