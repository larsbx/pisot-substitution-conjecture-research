// Independent bounded scalar/address model of actual-prefix norm bounds.
// Rational inequalities are cleared by a strictly positive denominator.
// All forall tests enumerate their declared finite domains. No Pisot
// realization, infinite word, compactness theorem or native packet is imported.
module C4StablePrefixDefinitions {
  pure def radiusSafe(den, num, digit, radius) =
    num * radius + den * digit <= den * radius
  pure def parameters(den, num, digit, radius) = all {
    den > 0, num >= 0, num < den, digit >= 0, radius >= 0,
    radiusSafe(den, num, digit, radius),
  }
  pure def stepInequality(den, num, digit, x, y) =
    den * x <= num * y + den * digit
  pure def stepPremises(den, num, digit, radius, x, y) = all {
    parameters(den, num, digit, radius), x >= 0, y >= 0,
    y <= radius, stepInequality(den, num, digit, x, y),
  }
  pure def selfPremises(den, num, digit, radius, x) = all {
    parameters(den, num, digit, radius), x >= 0,
    stepInequality(den, num, digit, x, x),
  }
  pure def stepConsequence(den, num, digit, radius, x, y) =
    not(stepPremises(den, num, digit, radius, x, y)) or x <= radius
  pure def selfConsequence(den, num, digit, radius, x) =
    not(selfPremises(den, num, digit, radius, x)) or x <= radius

  pure def positions(xs) = 0.to(xs.length() - 1)
  pure def orderedParents(parents) = positions(parents).forall(i =>
    parents[i] >= 0 and parents[i] <= i)
  pure def arrayPremises(den, num, digit, radius, values, parents) = {
    val shape = values.length() > 0 and values.length() == parents.length()
    // Short-circuiting keeps every parent lookup inside the supplied array.
    shape and orderedParents(parents) and parameters(den, num, digit, radius) and
      positions(values).forall(i => values[i] >= 0 and
        stepInequality(den, num, digit, values[i], values[parents[i]]))
  }
  pure def arrayConsequence(den, num, digit, radius, values, parents) =
    not(arrayPremises(den, num, digit, radius, values, parents)) or
      positions(values).forall(i => values[i] <= radius)
  pure def vector3(code, base) = List(
    code % base, (code / base) % base, (code / (base * base)) % base)

  // A digit record contains its source letter, literal position and norm.
  // This model's numbers are abstract exact data, not stable coordinates.
  pure def sameDigits(expected, supplied) = expected == supplied
  pure def digitsBounded(digits, bound) =
    positions(digits).forall(i => digits[i]._3 >= 0 and digits[i]._3 <= bound)
  pure def sameBlock(expected, supplied) = expected == supplied
  pure def digitAdmission(expected, supplied, expectedBlock, suppliedBlock, bound) = all {
    expectedBlock > 0, suppliedBlock > 0, bound >= 0,
    sameBlock(expectedBlock, suppliedBlock), sameDigits(expected, supplied),
    digitsBounded(supplied, bound),
  }
}

module C4StablePrefixScalar {
  import C4StablePrefixDefinitions.*
  var active: bool
  action init = active' = true

  pure val denominators = 1.to(4)
  pure val numerators = 0.to(3)
  pure val digits = 0.to(2)
  pure val radii = 0.to(6)
  pure val childNorms = 0.to(12)
  pure val parentNorms = 0.to(8)

  run scalarDomainCountTest = init.expect(all {
    active, denominators.size() == 4, numerators.size() == 4,
    digits.size() == 3, radii.size() == 7,
    childNorms.size() == 13, parentNorms.size() == 9,
    denominators.size() * numerators.size() * digits.size() * radii.size() *
      childNorms.size() * parentNorms.size() == 39312,
    denominators.size() * numerators.size() * digits.size() * radii.size() *
      childNorms.size() == 4368,
  })

  run exhaustiveParentStepTest = init.expect(denominators.forall(den =>
    numerators.forall(num => digits.forall(digit => radii.forall(radius =>
      childNorms.forall(x => parentNorms.forall(y =>
        stepConsequence(den, num, digit, radius, x, y))))))))

  run exhaustiveSelfParentTest = init.expect(denominators.forall(den =>
    numerators.forall(num => digits.forall(digit => radii.forall(radius =>
      childNorms.forall(x => selfConsequence(den, num, digit, radius, x)))))))

  run acceptedBoundaryAndZeroTest = init.expect(all {
    stepPremises(2, 1, 1, 2, 2, 2), selfPremises(2, 1, 1, 2, 2),
    radiusSafe(2, 1, 1, 2), parameters(1, 0, 0, 0),
    selfPremises(1, 0, 0, 0, 0), not(selfPremises(1, 0, 0, 0, 1)),
    stepPremises(4, 3, 1, 4, 3, 3), selfPremises(4, 3, 1, 4, 4),
  })

  // The existing native fixture's constants, only as a cleared arithmetic
  // calibration here; this test does not prove its norm or digit premises.
  run existingRadiusArithmeticTest = init.expect(all {
    parameters(8, 7, 5, 40), 7 * 40 + 8 * 5 == 8 * 40,
    selfPremises(8, 7, 5, 40, 40), not(selfPremises(8, 7, 5, 40, 41)),
  })
}

module C4StablePrefixArrays {
  import C4StablePrefixDefinitions.*
  var active: bool
  action init = active' = true
  pure val parentCodes = 0.to(26)
  pure val valueCodes = 0.to(124)
  pure val configs = Set((2, 1, 1, 2), (3, 2, 1, 3), (1, 0, 0, 0), (4, 3, 1, 4))

  run arrayDomainCountTest = init.expect(all {
    active, parentCodes.map(c => vector3(c, 3)).size() == 27,
    parentCodes.filter(c => orderedParents(vector3(c, 3))).size() == 6,
    valueCodes.map(c => vector3(c, 5)).size() == 125, configs.size() == 4,
    parentCodes.size() * valueCodes.size() * configs.size() == 13500,
  })

  // Every one of 27 parent arrays, 125 norm arrays and 4 parameter tuples
  // is checked. The 6 nonincreasing-parent arrays include every self-loop.
  run exhaustiveWholeArrayTest = init.expect(parentCodes.forall(p =>
    valueCodes.forall(v => configs.forall(c =>
      arrayConsequence(c._1, c._2, c._3, c._4, vector3(v, 5), vector3(p, 3))))))

  run selfLoopsAndEarlierParentsTest = init.expect(all {
    arrayPremises(2, 1, 1, 2, List(2, 2, 2), List(0, 1, 2)),
    arrayPremises(2, 1, 1, 2, List(0, 1, 1), List(0, 0, 1)),
    arrayPremises(1, 0, 0, 0, List(0, 0, 0), List(0, 1, 0)),
    not(arrayPremises(2, 1, 1, 2, List(0, 1, 3), List(0, 0, 1))),
  })

  run incompleteArrayRefusedTest = init.expect(all {
    not(arrayPremises(2, 1, 1, 2, List(0, 1, 9), List(0, 0))),
    not(arrayPremises(2, 1, 1, 2, List(), List())),
    not(orderedParents(List(0, -1, 0))),
    not(orderedParents(List(0, 0, 3))),
  })
}

module C4StablePrefixAdversarial {
  import C4StablePrefixDefinitions.*
  var active: bool
  action init = active' = true

  run strictContractionRefusedTest = init.expect(all {
    active, radiusSafe(1, 1, 0, 0), stepInequality(1, 1, 0, 1, 1), 1 > 0,
    not(parameters(1, 1, 0, 0)), not(selfPremises(1, 1, 0, 0, 1)),
  })

  run invariantRadiusRefusedTest = init.expect(all {
    stepInequality(2, 1, 1, 2, 2), 2 > 0,
    not(radiusSafe(2, 1, 1, 0)), not(parameters(2, 1, 1, 0)),
    not(selfPremises(2, 1, 1, 0, 2)),
  })

  run negativeNumeratorRefusedTest = init.expect(all {
    radiusSafe(1, -1, 2, 1), stepInequality(1, -1, 2, 2, 0), 0 <= 1, 2 > 1,
    not(parameters(1, -1, 2, 1)),
  })

  run invalidSignsRefusedTest = init.expect(all {
    not(parameters(0, 0, 0, 0)), not(parameters(-1, 0, 0, 0)),
    not(parameters(2, 1, -1, 2)), not(parameters(2, 1, 0, -1)),
  })

  // Infinite forward ancestry has the explicit formula x_n=2^n,
  // parent(n)=n+1, q=1/2,D=R=0. The following finite segment exhibits four
  // exact local equations and a fifth, exposed endpoint. It is not a closed
  // finite-array counterexample: any such fully closed contracting array
  // is bounded by its own maximum even without this ordinal discipline.
  run laterParentRefusedTest = init.expect({
    val values = List(1, 2, 4, 8, 16)
    val parents = List(1, 2, 3, 4)
    all {
      parameters(2, 1, 0, 0),
      positions(parents).forall(i => stepInequality(2, 1, 0, values[i], values[parents[i]])),
      positions(values).forall(i => values[i] > 0),
      not(orderedParents(parents)),
      not(arrayPremises(2, 1, 0, 0, values, parents)),
    }
  })

  run selfParentMustRemainAdmittedTest = init.expect(all {
    orderedParents(List(0, 1, 2)),
    arrayPremises(2, 1, 1, 2, List(2, 2, 2), List(0, 1, 2)),
  })

  run omittedDigitRefusedTest = init.expect({
    val expected = List((0, 0, 0), (0, 1, 3))
    val supplied = List((0, 0, 0))
    all {
      digitsBounded(supplied, 0), not(digitsBounded(expected, 0)),
      not(digitAdmission(expected, supplied, 2, 2, 0)),
      digitAdmission(expected, expected, 2, 2, 3),
    }
  })

  run wrongBlockRefusedTest = init.expect({
    val digits = List((0, 0, 0), (0, 1, 1))
    all {
      digitsBounded(digits, 1), not(sameBlock(12, 2)),
      not(digitAdmission(digits, digits, 12, 2, 1)),
      digitAdmission(digits, digits, 12, 12, 1),
    }
  })

  run underestimatedDigitRefusedTest = init.expect({
    val digits = List((0, 0, 0), (0, 1, 3))
    all {
      sameDigits(digits, digits), sameBlock(2, 2),
      not(digitAdmission(digits, digits, 2, 2, 2)),
      digitAdmission(digits, digits, 2, 2, 3),
    }
  })

  run repeatedPositionIdentityTest = init.expect({
    val expected = List((0, 0, 1), (0, 1, 1))
    val changed = List((0, 0, 1), (0, 0, 1))
    all {
      digitsBounded(expected, 1), digitsBounded(changed, 1),
      expected.length() == changed.length(),
      not(digitAdmission(expected, changed, 2, 2, 1)),
    }
  })
}
