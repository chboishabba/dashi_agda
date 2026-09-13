module DASHI.Physics.Closure.NSTriadKNLiteralSelfFluxFiniteDerivativeCompilerRound559Exact where

------------------------------------------------------------------------
-- ROUND559 / REUSE THE OLD R416--R427 TEMPORAL COMPILER ON THE SELF-FLUX
--
-- R548--R558 reduce the diagonal contribution to one favourable self-Gram
-- term and the actual time derivative of a finite R290 self-flux.  The older
-- temporal lane already contains all generic differentiation machinery:
--
--   R417  Hermitian product rule -> exact R291 Gram tangent
--   R416  fixed resolvent weight -> exact R290 weighted-flux tangent
--   R418  same R291/R290 pair carrier weld
--   R412  finite scalar sum differentiation
--   R425--R427 actual literal mixed-cell differentiation from the live RHS.
--
-- This owner reuses R422's composition of R416/R417/R418/R412 and retargets
-- it to ANY finite self-flux whose term lists are proved to be the same
-- observable.  It introduces no second derivative semantics and no new NS
-- estimate.  The remaining physical seam is therefore only to enumerate the
-- literal self-pair curves with time-fixed resolvent weights and weld their
-- finite sums to R549/R550 (and then R555/R556 globally).
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
import DASHI.Physics.Closure.NSTriadKNR418FinitePairFamilyToR409Round422Exact as R422
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNLiteralTrajectoryMixedCellDerivativeRound427Exact as R427
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = Rational.rationalRealField

record LiteralSelfFluxFiniteFamily559
    (Time : Set)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (selfFlux selfFluxTangent : Time → ℚ) : Set₁ where
  constructor literal-self-flux-finite-family-559
  field
    pairCurves : List (R422.PairCurveDerivativeData Time VectorDerivativeOf)

    fluxSumIsLiteralSelfFlux :
      (time : Time) →
      R412.sumCurves (R422.fluxTerms pairCurves) time ≡ selfFlux time

    tangentSumIsLiteralSelfFluxTangent :
      (time : Time) →
      R412.sumCurves (R422.tangentTerms pairCurves) time
      ≡ selfFluxTangent time

open LiteralSelfFluxFiniteFamily559 public

module Compile
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf :
      (Time → ℚ) →
      (Time → ℚ) → Set)
    (H : R417.HermitianDerivativeCalculus
      Time VectorDerivativeOf ScalarDerivativeOf)
    (C : R416.ScalarConstantDerivativeCalculus
      Time ScalarDerivativeOf)
    (A : R412.ScalarDerivativeAlgebra Time ScalarDerivativeOf) where

  module Existing = R422.FiniteFamily
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf H C A

  literalSelfFluxFamilyBuildsExactDerivative559 :
    (selfFlux selfFluxTangent : Time → ℚ) →
    LiteralSelfFluxFiniteFamily559
      Time VectorDerivativeOf selfFlux selfFluxTangent →
    ScalarDerivativeOf selfFlux selfFluxTangent
  literalSelfFluxFamilyBuildsExactDerivative559 selfFlux selfFluxTangent P =
    R412.transportDerivative A
      (fluxSumIsLiteralSelfFlux P)
      (tangentSumIsLiteralSelfFluxTangent P)
      (R412.finiteSumDerivative A
        (Existing.allPairDerivatives (pairCurves P)))

------------------------------------------------------------------------
-- Dependency audit.
------------------------------------------------------------------------

data R559Residual : Set where
  missingLiteralSelfPairCurveEnumeration559 : R559Residual
  missingOrdinaryScalarFTC559 : R559Residual
  missingFactoredFullSpacetimeBound559 : R559Residual
  literalLeafAFromNormalFormClosed559 : R559Residual

currentR559Residual : R559Residual
currentR559Residual = missingLiteralSelfPairCurveEnumeration559

round559HermitianProductRuleReused : Bool
round559HermitianProductRuleReused =
  R417.round417OnlyHermitianProductRuleNeededAfterCellDerivatives

round559FixedResolventDerivativeCompilerReused : Bool
round559FixedResolventDerivativeCompilerReused =
  R416.round416ResolventWeightDifferentiationReducedToConstantScale

round559FiniteSumDerivativeCompilerReused : Bool
round559FiniteSumDerivativeCompilerReused =
  R422.round422FinitePairSummationClosed

round559ActualLiteralMixedCellDerivativeProducerAvailable : Bool
round559ActualLiteralMixedCellDerivativeProducerAvailable =
  R427.round427ActualPlusMinusCellDifferentiationClosedModuloStandardCalculus

round559DoubleMixedDerivativeCompilerAvailable : Bool
round559DoubleMixedDerivativeCompilerAvailable =
  R425.round425DoubleMixedActualDerivativeReducedToTwoPlusMinusDerivatives

round559LiteralSelfPairCurveEnumerationClosed : Bool
round559LiteralSelfPairCurveEnumerationClosed = false

round559IntroducesNewDerivativeInterface : Bool
round559IntroducesNewDerivativeInterface = false

round559LiteralR406SignedCrossPaymentClosed : Bool
round559LiteralR406SignedCrossPaymentClosed = false

round559CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round559CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round559ClayPromotion : Bool
round559ClayPromotion = false

round559FiniteSumDerivativeCompilerReusedIsTrue :
  round559FiniteSumDerivativeCompilerReused ≡ true
round559FiniteSumDerivativeCompilerReusedIsTrue =
  R422.round422FinitePairSummationClosedIsTrue

-- R427 exposes the closed Bool but not a separate IsTrue theorem.  Keep the
-- status value itself as the imported receipt rather than inventing an alias.

round559IntroducesNewDerivativeInterfaceIsFalse :
  round559IntroducesNewDerivativeInterface ≡ false
round559IntroducesNewDerivativeInterfaceIsFalse = refl

round559ClayPromotionIsFalse : round559ClayPromotion ≡ false
round559ClayPromotionIsFalse = refl
