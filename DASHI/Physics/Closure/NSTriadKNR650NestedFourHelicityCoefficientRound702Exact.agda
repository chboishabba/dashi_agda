{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650NestedFourHelicityCoefficientRound702Exact where

------------------------------------------------------------------------
-- ROUND702 / EXPOSE THE ACTUAL FOUR HELICAL MULTIPLIER COEFFICIENTS
--
-- R700/R701 reduce the Clay-facing nonlinear object to the complete
-- outer-three-leg / inner-four-helicity incidence kernel.  Before estimating
-- that kernel, expose the literal scalar multiplying each projected cross.
--
-- For an inner incidence a+b=p and helicity signs s,t,
--
--   M_st = (lambda_t(b)-lambda_s(a))
--          P_p(u_a^s x u_b^t).
--
-- Hence the four channels are exactly
--
--   ++ : (+|b|) - (+|a|)
--   +- : (-|b|) - (+|a|)
--   -+ : (+|b|) - (-|a|)
--   -- : (-|b|) - (-|a|).
--
-- In ordinary scalar notation these are respectively
--
--   |b|-|a|,  -( |a|+|b| ),  |a|+|b|,  |a|-|b|.
--
-- This file deliberately stops before claiming cancellation: the four
-- coefficients multiply four different projected helical cross vectors.
-- Any exact cancellation must therefore use vector/helicity/orbit structure,
-- not the scalar coefficients alone.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNInnerHelicalComponentCommutatorRound571Exact as R571

module CoefficientNormalForm
    {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode)) where

  module C = R571.Componentwise system S L velocityTransverse

  channelCoefficient :
    Physical.PhysicalTriadIncidence →
    Helical.HelicitySign →
    Helical.HelicitySign →
    C3.Complex F
  channelCoefficient tau signA signB =
    C3.complexSubtract
      (C.signedEigenvalue signB (Physical.q tau))
      (C.signedEigenvalue signA (Physical.p tau))

  projectedHelicalCross :
    Physical.PhysicalTriadIncidence →
    Helical.HelicitySign →
    Helical.HelicitySign →
    C3.Complex3 F
  projectedHelicalCross tau signA signB =
    C3.lerayProject3 E I (Physical.k tau)
      (Cross.complex3Cross
        (C.component signA (Physical.p tau))
        (C.component signB (Physical.q tau)))

  multiplierDifferenceIsCoefficientTimesProjectedCross :
    (tau : Physical.PhysicalTriadIncidence) →
    (signA signB : Helical.HelicitySign) →
    C.multiplierDifferenceVector tau signA signB
    ≡
    C3.complex3Scale
      (channelCoefficient tau signA signB)
      (projectedHelicalCross tau signA signB)
  multiplierDifferenceIsCoefficientTimesProjectedCross tau signA signB = refl

  plusPlusCoefficient :
    (tau : Physical.PhysicalTriadIncidence) →
    channelCoefficient tau Helical.plus Helical.plus
    ≡
    C3.complexSubtract
      (C3.realEmbed F (Helical.modeNorm S (Physical.q tau)))
      (C3.realEmbed F (Helical.modeNorm S (Physical.p tau)))
  plusPlusCoefficient tau = refl

  plusMinusCoefficient :
    (tau : Physical.PhysicalTriadIncidence) →
    channelCoefficient tau Helical.plus Helical.minus
    ≡
    C3.complexSubtract
      (C3.realEmbed F
        (C3.negate F (Helical.modeNorm S (Physical.q tau))))
      (C3.realEmbed F (Helical.modeNorm S (Physical.p tau)))
  plusMinusCoefficient tau = refl

  minusPlusCoefficient :
    (tau : Physical.PhysicalTriadIncidence) →
    channelCoefficient tau Helical.minus Helical.plus
    ≡
    C3.complexSubtract
      (C3.realEmbed F (Helical.modeNorm S (Physical.q tau)))
      (C3.realEmbed F
        (C3.negate F (Helical.modeNorm S (Physical.p tau))))
  minusPlusCoefficient tau = refl

  minusMinusCoefficient :
    (tau : Physical.PhysicalTriadIncidence) →
    channelCoefficient tau Helical.minus Helical.minus
    ≡
    C3.complexSubtract
      (C3.realEmbed F
        (C3.negate F (Helical.modeNorm S (Physical.q tau))))
      (C3.realEmbed F
        (C3.negate F (Helical.modeNorm S (Physical.p tau))))
  minusMinusCoefficient tau = refl

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round702LiteralFourHelicityScalarCoefficientsExposed : Bool
round702LiteralFourHelicityScalarCoefficientsExposed = true

round702EachChannelRemainsPairedWithItsOwnProjectedCrossVector : Bool
round702EachChannelRemainsPairedWithItsOwnProjectedCrossVector = true

round702ScalarCoefficientCancellationAloneClosesOrbit : Bool
round702ScalarCoefficientCancellationAloneClosesOrbit = false

round702IntroducesEstimate : Bool
round702IntroducesEstimate = false

round702IntroducesNormOrAbsoluteValue : Bool
round702IntroducesNormOrAbsoluteValue = false

round702NestedOrbitSignedPaymentClosed : Bool
round702NestedOrbitSignedPaymentClosed = false

round702ClayPromotion : Bool
round702ClayPromotion = false

round702LiteralFourHelicityScalarCoefficientsExposedIsTrue :
  round702LiteralFourHelicityScalarCoefficientsExposed ≡ true
round702LiteralFourHelicityScalarCoefficientsExposedIsTrue = refl

round702EachChannelRemainsPairedWithItsOwnProjectedCrossVectorIsTrue :
  round702EachChannelRemainsPairedWithItsOwnProjectedCrossVector ≡ true
round702EachChannelRemainsPairedWithItsOwnProjectedCrossVectorIsTrue = refl

round702ScalarCoefficientCancellationAloneClosesOrbitIsFalse :
  round702ScalarCoefficientCancellationAloneClosesOrbit ≡ false
round702ScalarCoefficientCancellationAloneClosesOrbitIsFalse = refl

round702IntroducesEstimateIsFalse :
  round702IntroducesEstimate ≡ false
round702IntroducesEstimateIsFalse = refl

round702IntroducesNormOrAbsoluteValueIsFalse :
  round702IntroducesNormOrAbsoluteValue ≡ false
round702IntroducesNormOrAbsoluteValueIsFalse = refl

round702NestedOrbitSignedPaymentClosedIsFalse :
  round702NestedOrbitSignedPaymentClosed ≡ false
round702NestedOrbitSignedPaymentClosedIsFalse = refl

round702ClayPromotionIsFalse :
  round702ClayPromotion ≡ false
round702ClayPromotionIsFalse = refl
