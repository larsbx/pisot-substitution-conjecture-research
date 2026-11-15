// Independent finite controls for coordinate norms and chart authentication.
// Every rational inequality is cleared by positive integer denominators.
// These are bounded integer models, not a real-root or Pisot certificate.
module C4NamedChartDefinitions {
  pure def absI(x) = if (x < 0) -x else x
  pure def maxI(x, y) = if (x < y) y else x
  pure def norm2(x) = maxI(absI(x[0]), absI(x[1]))
  pure def norm3(x) = maxI(maxI(absI(x[0]), absI(x[1])), absI(x[2]))
  pure def matrix(a, b, c, d) = List(List(a, b), List(c, d))
  pure def apply2(m, x) = List(
    m[0][0] * x[0] + m[0][1] * x[1],
    m[1][0] * x[0] + m[1][1] * x[1])
  pure def row0(m) = absI(m[0][0]) + absI(m[0][1])
  pure def row1(m) = absI(m[1][0]) + absI(m[1][1])
  pure def rowNorm(m) = maxI(row0(m), row1(m))
  pure def columnNorm(m) = maxI(
    absI(m[0][0]) + absI(m[1][0]), absI(m[0][1]) + absI(m[1][1]))
  pure def entryNorm(m) = maxI(
    maxI(absI(m[0][0]), absI(m[0][1])),
    maxI(absI(m[1][0]), absI(m[1][1])))
  pure def parameters(den, num, qden) = all {
    den > 0, qden > 0, num >= 0, num < qden,
  }
  pure def rowsSafe(m, den, num, qden) = all {
    qden * row0(m) <= num * den,
    qden * row1(m) <= num * den,
  }
  pure def admitted(m, den, num, qden) =
    parameters(den, num, qden) and rowsSafe(m, den, num, qden)
  pure def consequence(m, den, num, qden, x) =
    not(admitted(m, den, num, qden)) or
      qden * norm2(apply2(m, x)) <= num * den * norm2(x)
  pure def matrixOf(code) = matrix(
    code % 3 - 1, (code / 3) % 3 - 1,
    (code / 9) % 3 - 1, (code / 27) % 3 - 1)
  pure def vectorOf(code) = List(code % 5 - 2, (code / 5) % 5 - 2)
  pure def vector3Of(code) = List(
    code % 5 - 2, (code / 5) % 5 - 2, (code / 25) % 5 - 2)
  pure def signI(x) = if (x < 0) -1 else if (x > 0) 1 else 0
  pure def maximizingVector(m) = {
    val i = if (row0(m) >= row1(m)) 0 else 1
    List(signI(m[i][0]), signI(m[i][1]))
  }
  pure def sameMatrix(expected, supplied) = expected == supplied
  pure def sameBlock(expected, supplied) = expected == supplied
  pure def certificate(expected, supplied, expectedBlock, suppliedBlock, den, num, qden) = all {
    expectedBlock > 0, suppliedBlock > 0,
    sameMatrix(expected, supplied), sameBlock(expectedBlock, suppliedBlock),
    admitted(supplied, den, num, qden),
  }

  pure def chart(a, b) = List(List(1, -a, 0), List(0, -b, 1))
  pure def applyChart(w, z) = List(
    w[0][0] * z[0] + w[0][1] * z[1] + w[0][2] * z[2],
    w[1][0] * z[0] + w[1][1] * z[1] + w[1][2] * z[2])
  pure def section(y) = List(y[0], 0, y[1])
  pure val basis2 = Set(List(1, 0), List(0, 1))
  pure val basis3 = Set(List(1, 0, 0), List(0, 1, 0), List(0, 0, 1))
  // A separate exact algebraic control, not the named Pisot incidence.
  pure def toyAction(z) = List(z[0], 2 * z[1], z[2])
  pure def sectionIdentity(w) = basis2.forall(y => applyChart(w, section(y)) == y)
  pure def basisCommutation(w) = basis3.forall(z =>
    applyChart(w, toyAction(z)) == applyChart(w, z))
  pure def quotientAdmission(w) = all {
    sectionIdentity(w),
    basisCommutation(w),
  }
  // For chart(1,1), kernel vector r=(1,1,1), ell=(1,2,1), ell(r)=4.
  // lift4 is four times the true section into ker(ell), with no division.
  pure def physical(z) = z[0] + 2 * z[1] + z[2]
  pure def lift4(y) = {
    val s = y[0] + y[1]
    List(4 * y[0] - s, -s, 4 * y[1] - s)
  }
}

module C4NamedChartExhaustive {
  import C4NamedChartDefinitions.*
  var active: bool
  action init = active' = true
  pure val matrices = 0.to(80).map(code => matrixOf(code))
  pure val vectors = 0.to(24).map(code => vectorOf(code))
  pure val denominators = 1.to(3)
  pure val numerators = 0.to(2)
  pure val qdenominators = 1.to(3)

  run matrixDomainCountTest = init.expect(all {
    active, matrices.size() == 81, vectors.size() == 25,
    matrices.size() * vectors.size() == 2025,
    matrices.size() * vectors.size() * denominators.size() *
      numerators.size() * qdenominators.size() == 54675,
  })
  run exhaustiveRowBoundTest = init.expect(matrices.forall(m => vectors.forall(x =>
    norm2(apply2(m, x)) <= rowNorm(m) * norm2(x))))
  run exhaustiveRationalContractionTest = init.expect(matrices.forall(m => vectors.forall(x =>
    denominators.forall(den => numerators.forall(num => qdenominators.forall(qden =>
      consequence(m, den, num, qden, x)))))))
  run exactSignedExtremizerTest = init.expect(matrices.forall(m =>
    norm2(apply2(m, maximizingVector(m))) == rowNorm(m)))
  run nonvacuousBoundaryTest = init.expect(all {
    admitted(matrix(1, 0, 0, 1), 2, 1, 2),
    consequence(matrix(1, 0, 0, 1), 2, 1, 2, List(-2, 2)),
    admitted(matrix(0, 0, 0, 0), 1, 0, 1),
    admitted(matrix(1, 1, 0, 1), 4, 1, 2),
    2 * norm2(apply2(matrix(1, 1, 0, 1), List(1, 1))) == 4,
  })
}

module C4NamedChartAlgebra {
  import C4NamedChartDefinitions.*
  var active: bool
  action init = active' = true
  pure val coefficients = (-2).to(2)
  pure val vectors = 0.to(24).map(code => vectorOf(code))
  pure val vectors3 = 0.to(124).map(code => vector3Of(code))

  run completeSectionFamilyTest = init.expect(all {
    active, coefficients.size() * coefficients.size() * vectors.size() == 625,
    coefficients.forall(a => coefficients.forall(b => vectors.forall(y =>
      applyChart(chart(a, b), section(y)) == y))),
  })
  run correctedSectionTest = init.expect(vectors.forall(y => all {
    physical(lift4(y)) == 0,
    applyChart(chart(1, 1), lift4(y)) == List(4 * y[0], 4 * y[1]),
  }))
  run fullReconstructionTest = init.expect(vectors3.forall(z => {
    val lifted = lift4(applyChart(chart(1, 1), z))
    val p = physical(z)
    List(lifted[0] + p, lifted[1] + p, lifted[2] + p) ==
      List(4 * z[0], 4 * z[1], 4 * z[2])
  }))
  run basisCommutationFamilyTest = init.expect(all {
    coefficients.size() * coefficients.size() * vectors3.size() == 3125,
    quotientAdmission(chart(0, 0)),
    coefficients.forall(a => coefficients.forall(b => vectors3.forall(z =>
      not(basisCommutation(chart(a, b))) or
        applyChart(chart(a, b), toyAction(z)) == applyChart(chart(a, b), z)))),
  })
}

module C4NamedChartAdversarial {
  import C4NamedChartDefinitions.*
  var active: bool
  action init = active' = true

  run columnNormRefusedTest = init.expect({
    val m = matrix(6, 6, 1, 0)
    all {
      active, columnNorm(m) == 7, 8 * columnNorm(m) <= 7 * 10,
      8 * norm2(apply2(m, List(1, 1))) > 7 * 10,
      not(admitted(m, 10, 7, 8)),
    }
  })
  run entrywiseNormRefusedTest = init.expect({
    val m = matrix(6, 6, 0, 6)
    all {
      entryNorm(m) == 6, 8 * entryNorm(m) <= 7 * 10,
      8 * norm2(apply2(m, List(1, 1))) > 7 * 10,
      not(admitted(m, 10, 7, 8)),
    }
  })
  run signedCancellationRefusedTest = init.expect({
    val m = matrix(-1, -1, 0, -1)
    all {
      norm2(apply2(m, List(1, 1))) == 2,
      not(admitted(m, 2, 0, 1)),
    }
  })
  run secondRowRefusedTest = init.expect({
    val m = matrix(0, 0, 6, 6)
    all {
      row0(m) == 0, 8 * row1(m) > 7 * 10,
      not(admitted(m, 10, 7, 8)),
    }
  })
  run unitContractionRefusedTest = init.expect(all {
    rowsSafe(matrix(1, 0, 0, 1), 1, 1, 1),
    not(admitted(matrix(1, 0, 0, 1), 1, 1, 1)),
  })
  run invalidDenominatorRefusedTest = init.expect(all {
    rowsSafe(matrix(0, 0, 0, 0), 0, 0, 1),
    not(admitted(matrix(0, 0, 0, 0), 0, 0, 1)),
    not(admitted(matrix(0, 0, 0, 0), 1, 0, 0)),
    not(parameters(-1, 0, 1)), not(parameters(1, -1, 2)),
  })
  run wrongMatrixRefusedTest = init.expect(all {
    admitted(matrix(0, 0, 0, 0), 4, 1, 2),
    not(certificate(matrix(1, 1, 0, 1), matrix(0, 0, 0, 0), 12, 12, 4, 1, 2)),
  })
  run wrongBlockRefusedTest = init.expect(all {
    admitted(matrix(1, 1, 0, 1), 4, 1, 2),
    not(certificate(matrix(1, 1, 0, 1), matrix(1, 1, 0, 1), 12, 2, 4, 1, 2)),
    certificate(matrix(1, 1, 0, 1), matrix(1, 1, 0, 1), 12, 12, 4, 1, 2),
  })
  run zeroProjectionRefusedTest = init.expect({
    val w = List(List(0, 0, 0), List(0, 0, 0))
    all { basisCommutation(w), not(quotientAdmission(w)) }
  })
  run missingCommutationRefusedTest = init.expect(all {
    sectionIdentity(chart(1, 0)),
    not(quotientAdmission(chart(1, 0))),
  })
  run coordinateRescalingRefusedTest = init.expect(all {
    // diag(4,1) conjugates the first rational matrix into the second.
    admitted(matrix(1, 1, 0, 1), 4, 1, 2),
    not(admitted(matrix(1, 4, 0, 1), 4, 1, 2)),
    norm2(apply2(matrix(1, 4, 0, 1), List(1, 1))) == 5,
    5 > 4,
  })
  run quotientNormNotIsometryTest = init.expect(all {
    // A representative of half the coordinate norm exists in this quotient.
    applyChart(chart(1, 0), List(1, -1, 0)) == List(2, 0),
    norm3(List(1, -1, 0)) == 1,
    norm2(List(2, 0)) == 2,
  })
  run rawSectionNotStablePlaneTest = init.expect(all {
    applyChart(chart(1, 1), section(List(1, 0))) == List(1, 0),
    physical(section(List(1, 0))) == 1,
    physical(lift4(List(1, 0))) == 0,
  })
}
