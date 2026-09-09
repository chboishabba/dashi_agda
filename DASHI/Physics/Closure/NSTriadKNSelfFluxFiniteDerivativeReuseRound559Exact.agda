module DASHI.Physics.Closure.NSTriadKNSelfFluxFiniteDerivativeReuseRound559Exact where

------------------------------------------------------------------------
-- ROUND559 / FINITE SELF-FLUX DERIVATIVE REUSES R418 + R412
--
-- R551 asks only for the literal trajectory weld
--
--   selfFlux        = R393 flux
--   selfFluxTangent = R393 tangent.
--
-- The derivative calculus below is not new.  R418 already compiles one SAME
-- R291/R290 pair curve to the exact weighted R290 flux derivative once the two
-- literal cell derivatives are known.  R412 already compiles a finite family.
--
-- This owner retargets that existing finite compiler to an arbitrary explicit
-- self-flux/self-tangent pair.  Consequently finite summation is removed from
-- the R551 residual.  The only physical work left is to construct the actual
-- time-indexed self-pair family and prove the two final same-object equalities.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNR291R290SamePairDerivativeRound418Exact as R418
import DASHI.Physics.Closure.NSTriadKNR418FinitePairFamilyToR409Round422Exact as R422
import DASHI.Physics.Closure.NSTriadKNLiteralR406DiagonalFluxEndpointReuseRound551Exact as R551

F : C3.RealField _
F = Rational.rationalRealField

module SelfFluxFinite
    (Time : Set)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf : (Time → ℚ) → (Time → ℚ) → Set)
    (H : R417.HermitianDerivativeCalculus
      Time VectorDerivativeOf ScalarDerivativeOf)
    (C : R416.ScalarConstantDerivativeCalculus
      Time ScalarDerivativeOf)
    (A : R412.ScalarDerivativeAlgebra Time ScalarDerivativeOf) where

  module Pair = R418.SamePairDerivative
    Time VectorDerivativeOf ScalarDerivativeOf H C

  allPairDerivatives :
    (items : List (R422.PairCurveDerivativeData Time VectorDerivativeOf)) →
    R412.AllDerivatives ScalarDerivativeOf
      (R422.fluxTerms items) (R422.tangentTerms items)
  allPairDerivatives = R422.FiniteFamily.allPairDerivatives
    Time _ _ VectorDerivativeOf ScalarDerivativeOf H C A

  record LiteralSelfFluxPairFamily559 : Set₁ where
    field
      pairCurves559 : List (R422.PairCurveDerivativeData Time VectorDerivativeOf)

      selfFlux559 : Time → ℚ
      selfFluxTangent559 : Time → ℚ

      fluxSumIsLiteralSelfFlux559 :
        (time : Time) →
        R412.sumCurves (R422.fluxTerms pairCurves559) time
        ≡ selfFlux559 time

      tangentSumIsLiteralSelfFluxTangent559 :
        (time : Time) →
        R412.sumCurves (R422.tangentTerms pairCurves559) time
        ≡ selfFluxTangent559 time

  open LiteralSelfFluxPairFamily559 public

  literalSelfFluxFamilyBuildsDerivative559 :
    (P : LiteralSelfFluxPairFamily559) →
    ScalarDerivativeOf (selfFlux559 P) (selfFluxTangent559 P)
  literalSelfFluxFamilyBuildsDerivative559 P =
    R412.transportDerivative A
      (fluxSumIsLiteralSelfFlux559 P)
      (tangentSumIsLiteralSelfFluxTangent559 P)
      (R412.finiteSumDerivative A
        (allPairDerivatives (pairCurves559 P)))

------------------------------------------------------------------------
-- Proof-search boundary.
------------------------------------------------------------------------

data R559Residual : Set where
  missingLiteralR240SelfPairFamily559 : R559Residual
  missingFixedSelfPairResolventWeight559 : R559Residual
  missingR551FinalSameObjectWeld559 : R559Residual
  selfFluxTrajectoryDerivativeClosed559 : R559Residual

currentR559Residual : R559Residual
currentR559Residual = missingLiteralR240SelfPairFamily559

round559ReusesR418PerPairDerivative : Bool
round559ReusesR418PerPairDerivative = true

round559ReusesR412FiniteSumDerivative : Bool
round559ReusesR412FiniteSumDerivative = true

round559IntroducesNewDerivativeCalculus : Bool
round559IntroducesNewDerivativeCalculus = false

round559FiniteSelfFluxDifferentiationClosedGivenLiteralPairFamily : Bool
round559FiniteSelfFluxDifferentiationClosedGivenLiteralPairFamily = true

round559LiteralR240SelfPairFamilyConstructed : Bool
round559LiteralR240SelfPairFamilyConstructed = false

round559FixedSelfPairResolventWeightClosed : Bool
round559FixedSelfPairResolventWeightClosed = false

round559R551FinalSameObjectWeldClosed : Bool
round559R551FinalSameObjectWeldClosed = false

round559ClayPromotion : Bool
round559ClayPromotion = false

round559ReusesR418PerPairDerivativeIsTrue :
  round559ReusesR418PerPairDerivative ≡ true
round559ReusesR418PerPairDerivativeIsTrue = refl

round559IntroducesNewDerivativeCalculusIsFalse :
  round559IntroducesNewDerivativeCalculus ≡ false
round559IntroducesNewDerivativeCalculusIsFalse = refl

round559ClayPromotionIsFalse : round559ClayPromotion ≡ false
round559ClayPromotionIsFalse = refl
