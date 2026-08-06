module DASHI.Physics.Foundations.ModularProjectionQuantisationExact where

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicCarryResidualExact as Triadic

------------------------------------------------------------------------
-- Finite projection model for the attached axis-aligned / angled / coarse
-- comparisons.  The theorem surface isolates three effects:
--
--   * dropping coordinates is non-injective;
--   * an angled chart can separate a pair collapsed by an axis chart;
--   * coarse quantisation can collapse distinctions retained by a fine chart.
--
-- This does not infer a global optimum from rendered images.

record Point4 : Set where
  constructor point4
  field
    x0 : Nat
    y0 : Nat
    z0 : Nat
    w0 : Nat

open Point4 public

record Point2 : Set where
  constructor point2
  field
    u0 : Nat
    v0 : Nat

open Point2 public

axisProjection : Point4 → Point2
axisProjection p = point2 (x0 p) (y0 p)

angledProjection : Point4 → Point2
angledProjection p = point2 (x0 p + z0 p) (y0 p + w0 p)

pointA : Point4
pointA = point4 1 1 0 0

pointB : Point4
pointB = point4 1 1 1 0

axisProjectionCollapsesAB :
  axisProjection pointA ≡ axisProjection pointB
axisProjectionCollapsesAB = refl

angledProjectionSeparatesAB :
  angledProjection pointA ≡ angledProjection pointB → ⊥
angledProjectionSeparatesAB ()

------------------------------------------------------------------------
-- Finite search objective: retain the declared witness distinction.

data ProjectionCandidate : Set where
  axisCandidate : ProjectionCandidate
  angledCandidate : ProjectionCandidate

separationScore : ProjectionCandidate → Nat
separationScore axisCandidate = 0
separationScore angledCandidate = 1

selectedProjection : ProjectionCandidate
selectedProjection = angledCandidate

selectedProjectionHasUnitSeparation :
  separationScore selectedProjection ≡ 1
selectedProjectionHasUnitSeparation = refl

axisCandidateHasZeroSeparation :
  separationScore axisCandidate ≡ 0
axisCandidateHasZeroSeparation = refl

------------------------------------------------------------------------
-- Coarse integer search / storage can identify distinct fine coordinates.

data FineCoordinate : Set where
  fine0 : FineCoordinate
  fine1 : FineCoordinate
  fine2 : FineCoordinate
  fine3 : FineCoordinate

data CoarseCoordinate : Set where
  coarse0 : CoarseCoordinate
  coarse1 : CoarseCoordinate

quantiseCoarse : FineCoordinate → CoarseCoordinate
quantiseCoarse fine0 = coarse0
quantiseCoarse fine1 = coarse0
quantiseCoarse fine2 = coarse1
quantiseCoarse fine3 = coarse1

coarseQuantisationIsNonInjective :
  quantiseCoarse fine0 ≡ quantiseCoarse fine1
coarseQuantisationIsNonInjective = refl

fineCoordinatesRemainDistinct : fine0 ≡ fine1 → ⊥
fineCoordinatesRemainDistinct ()

------------------------------------------------------------------------
-- Triadic modular chart.  The chart uses the existing exact Z/3Z addition
-- rather than treating a rendered modular transform as ordinary Euclidean
-- addition.

record TriadicPoint4 : Set where
  constructor triadicPoint4
  field
    tx : Triadic.TriResidue
    ty : Triadic.TriResidue
    tz : Triadic.TriResidue
    tw : Triadic.TriResidue

open TriadicPoint4 public

record TriadicPoint2 : Set where
  constructor triadicPoint2
  field
    tu : Triadic.TriResidue
    tv : Triadic.TriResidue

open TriadicPoint2 public

modularAngledProjection : TriadicPoint4 → TriadicPoint2
modularAngledProjection p =
  triadicPoint2
    (Triadic.cyclicAdd3 (tx p) (tz p))
    (Triadic.cyclicAdd3 (ty p) (tw p))

triadicPointA : TriadicPoint4
triadicPointA =
  triadicPoint4
    Triadic.residue1
    Triadic.residue1
    Triadic.residue0
    Triadic.residue0

triadicPointB : TriadicPoint4
triadicPointB =
  triadicPoint4
    Triadic.residue1
    Triadic.residue1
    Triadic.residue1
    Triadic.residue0

modularProjectionA :
  modularAngledProjection triadicPointA
  ≡
  triadicPoint2 Triadic.residue1 Triadic.residue1
modularProjectionA = refl

modularProjectionB :
  modularAngledProjection triadicPointB
  ≡
  triadicPoint2 Triadic.residue2 Triadic.residue1
modularProjectionB = refl

record ModularProjectionQuantisationBoundary : Set where
  constructor modularProjectionQuantisationBoundary
  field
    oneRenderedComparisonProvesGlobalProjectionOptimality : Bool
    oneRenderedComparisonProvesGlobalProjectionOptimalityIsFalse :
      oneRenderedComparisonProvesGlobalProjectionOptimality ≡ false

    angledProjectionIsInjectiveFromFourDimensionsToTwo : Bool
    angledProjectionIsInjectiveFromFourDimensionsToTwoIsFalse :
      angledProjectionIsInjectiveFromFourDimensionsToTwo ≡ false

    coarseIntegerSearchPreservesAllFineDistinctions : Bool
    coarseIntegerSearchPreservesAllFineDistinctionsIsFalse :
      coarseIntegerSearchPreservesAllFineDistinctions ≡ false

    modularResidueChartIsOrdinaryEuclideanProjection : Bool
    modularResidueChartIsOrdinaryEuclideanProjectionIsFalse :
      modularResidueChartIsOrdinaryEuclideanProjection ≡ false

open ModularProjectionQuantisationBoundary public

canonicalModularProjectionQuantisationBoundary :
  ModularProjectionQuantisationBoundary
canonicalModularProjectionQuantisationBoundary =
  modularProjectionQuantisationBoundary
    false refl
    false refl
    false refl
    false refl
