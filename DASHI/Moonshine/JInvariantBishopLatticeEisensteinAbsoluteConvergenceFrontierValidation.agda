module DASHI.Moonshine.JInvariantBishopLatticeEisensteinAbsoluteConvergenceFrontierValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.JInvariantBishopLatticeEisensteinAbsoluteConvergenceFrontierExact as F

reciprocalPaid :
  F.bishopComplexReciprocalExact
    F.canonicalBishopLatticeEisensteinAbsoluteConvergenceFrontier
  ≡ true
reciprocalPaid = refl

upperHalfPlaneGeometryPaid :
  F.upperHalfPlaneDenominatorNonzeroExact
    F.canonicalBishopLatticeEisensteinAbsoluteConvergenceFrontier
  ≡ true
upperHalfPlaneGeometryPaid = refl

puncturedReindexingPaid :
  F.sl2zPuncturedLatticeReindexingExact
    F.canonicalBishopLatticeEisensteinAbsoluteConvergenceFrontier
  ≡ true
puncturedReindexingPaid = refl

squareCoverPaid :
  F.shellCardinalityBoundBySquareExact
    F.canonicalBishopLatticeEisensteinAbsoluteConvergenceFrontier
  ≡ true
squareCoverPaid = refl

coercivityPaid :
  F.divisionFreeLatticeCoercivityExact
    F.canonicalBishopLatticeEisensteinAbsoluteConvergenceFrontier
  ≡ true
coercivityPaid = refl

radiusSquareLowerPaid :
  F.squareShellRadiusSquareLowerBoundExact
    F.canonicalBishopLatticeEisensteinAbsoluteConvergenceFrontier
  ≡ true
radiusSquareLowerPaid = refl

firstResidualRegression :
  F.firstResidual
    F.canonicalBishopLatticeEisensteinAbsoluteConvergenceFrontier
  ≡ F.missingCoercivityToReciprocalPowerMajorant
firstResidualRegression = refl

absoluteSumStillOpen :
  F.puncturedAbsoluteSumConstructed
    F.canonicalBishopLatticeEisensteinAbsoluteConvergenceFrontier
  ≡ false
absoluteSumStillOpen = refl

fourierSameObjectStillOpen :
  F.qSeriesEqualsNormalizedLatticeE4E6
    F.canonicalBishopLatticeEisensteinAbsoluteConvergenceFrontier
  ≡ false
fourierSameObjectStillOpen = refl
