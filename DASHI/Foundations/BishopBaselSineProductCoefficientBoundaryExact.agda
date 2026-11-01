module DASHI.Foundations.BishopBaselSineProductCoefficientBoundaryExact where

------------------------------------------------------------------------
-- BASEL MEET-IN-THE-MIDDLE BOUNDARY
--
-- Two independent source chains now exist for the same finite Euler-product
-- linear coefficient sequence L_N:
--
--   L_N -> - BaselLimit
--
-- and, once the Euler sine-product coefficient theorem is supplied,
--
--   L_N -> - pi_M^2 / 6.
--
-- This module isolates ONLY that missing middle convergence theorem and proves
-- that it implies Basel immediately by uniqueness of Bishop limits.
------------------------------------------------------------------------

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Foundations.BishopBaselFiniteProductCoefficientLimitExact as ProductLimit
import DASHI.Foundations.BishopBaselReciprocalSquareConvergenceExact as Basel
import DASHI.Foundations.BishopBaselMachinSineQuadraticCoefficientExact as SineCoeff
open import DASHI.Physics.YangMills.CompactLieProofLevel

piSquareOverSix : BishopReal.ℝ
piSquareOverSix =
  BishopReal._*_
    SineCoeff.oneSixth
    (SineCoeff.square SineCoeff.machinPi)

record SineProductCoefficientLimit : Set₁ where
  field
    finiteProductLinearConvergesToSineCoefficient :
      BishopSequence._ConvergesTo_
        ProductLimit.embeddedFiniteProductLinear
        SineCoeff.normalizedSineQuadraticCoefficient

open SineProductCoefficientLimit public

negativeBaselEqualsSineCoefficient :
  SineProductCoefficientLimit →
  BishopReal._≃_
    (BishopReal.- Basel.baselLimit)
    SineCoeff.normalizedSineQuadraticCoefficient
negativeBaselEqualsSineCoefficient certificate =
  BishopSequence.uniqueness-of-limits
    ProductLimit.embeddedFiniteProductLinearConvergesNegativeBasel
    (finiteProductLinearConvergesToSineCoefficient certificate)

sineCoefficientIsNegativePiSquareOverSix :
  BishopReal._≃_
    SineCoeff.normalizedSineQuadraticCoefficient
    (BishopReal.- piSquareOverSix)
sineCoefficientIsNegativePiSquareOverSix = BishopP.≃-refl

baselFromSineProductCoefficientLimit :
  SineProductCoefficientLimit →
  BishopReal._≃_ Basel.baselLimit piSquareOverSix
baselFromSineProductCoefficientLimit certificate =
  let
    negativeEquality :
      BishopReal._≃_
        (BishopReal.- Basel.baselLimit)
        (BishopReal.- piSquareOverSix)
    negativeEquality =
      BishopP.≃-trans
        (negativeBaselEqualsSineCoefficient certificate)
        sineCoefficientIsNegativePiSquareOverSix
  in
  BishopP.≃-trans
    (BishopP.≃-symm (BishopP.neg-involutive Basel.baselLimit))
    (BishopP.≃-trans
      (BishopP.-‿cong negativeEquality)
      (BishopP.neg-involutive piSquareOverSix))

bishopBaselSineProductCoefficientBoundaryLevel : ProofLevel
bishopBaselSineProductCoefficientBoundaryLevel = machineChecked
