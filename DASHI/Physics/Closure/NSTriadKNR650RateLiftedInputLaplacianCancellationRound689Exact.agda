{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650RateLiftedInputLaplacianCancellationRound689Exact where

------------------------------------------------------------------------
-- ROUND689 / THE RATE-LIFTED C1 MINUS TANGENT CANCELLATION IS EXACTLY
--            EIGHT TIMES THE PHYSICAL INPUT-LAPLACIAN WORK
--
-- R688 proves on one nonzero physical fixed-output fibre
--
--   RateLiftedFull - 8 W(M,T) = 8 WeightedWork.
--
-- R684 identifies the SAME physical rate kernel exactly as
--
--   WeightedWork = nu W(M,L_in),
--
-- where
--
--   L_in = sum_{p+q=k} (|p|^2+|q|^2) A_{pq}.
--
-- Therefore
--
--   RateLiftedFull - 8 W(M,T)
--     = 8 nu W(M,L_in).
--
-- This removes the apparent quintic-vs-quartic mismatch only after preserving
-- the signed dynamic cancellation.  It does NOT say that the unlifted R568
-- budget controls the rate-lifted term, and it introduces no estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; Positive; _*_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact as D1a
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNR650RateKernelInputLaplacianCollapseRound684Exact as R684
import DASHI.Physics.Closure.NSTriadKNR650RateLiftedR568ToC2CommutatorRound687Exact as R687
import DASHI.Physics.Closure.NSTriadKNR650RateLiftedDynamicCancellationRound688Exact as R688

F : C3.RealField _
F = Rational.rationalRealField

module FixedOutput
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (viscosityPositive : Positive (Field30.viscosity physicalSystem))
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output) where

  module Cancel =
    R688.FixedOutput physicalSystem S viscosityPositive output outputNonzero

  system = Field30.finiteSystem physicalSystem
  cutoff = Audit.cutoff system
  velocity = Audit.velocityAt system
  I = Field30.physicalInverseSquare physicalSystem
  nu = Field30.viscosity physicalSystem
  value = D1a.mixedProductCell S velocity

  inputLaplacian =
    R684.inputLaplacianVector I value cutoff output

  inputLaplacianWork : ℚ
  inputLaplacianWork =
    nu * Work.coherentWork Cancel.mixed inputLaplacian

  weightedIsInputLaplacianWork :
    Cancel.weightedWork ≡ inputLaplacianWork
  weightedIsInputLaplacianWork =
    R684.fixedOutputPhysicalRateKernelIsInputLaplacianWork
      physicalSystem S output

  rateLiftedMinusTangentIsEightInputLaplacianWork :
    Cancel.rateLiftedFull - R687.eight * Cancel.tangentWork
    ≡ R687.eight * inputLaplacianWork
  rateLiftedMinusTangentIsEightInputLaplacianWork =
    trans
      Cancel.rateLiftedMinusTangentIsEightWeighted
      (cong (R687.eight *_) weightedIsInputLaplacianWork)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round689RateLiftedMinusTangentIsEightInputLaplacianWork : Bool
round689RateLiftedMinusTangentIsEightInputLaplacianWork = true

round689QuinticPiecesMustRemainCombinedBeforeQuarticCollapse : Bool
round689QuinticPiecesMustRemainCombinedBeforeQuarticCollapse = true

round689UnliftedR568BudgetControlsSignedRateLiftMinusTangent : Bool
round689UnliftedR568BudgetControlsSignedRateLiftMinusTangent = false

round689SignedRateLiftMinusTangentSpacetimePaymentClosed : Bool
round689SignedRateLiftMinusTangentSpacetimePaymentClosed = false

round689C1Closed : Bool
round689C1Closed = false

round689C2Closed : Bool
round689C2Closed = false

round689IntroducesEstimate : Bool
round689IntroducesEstimate = false

round689IntroducesNewClayLeaf : Bool
round689IntroducesNewClayLeaf = false

round689ClayPromotion : Bool
round689ClayPromotion = false

round689RateLiftedMinusTangentIsEightInputLaplacianWorkIsTrue :
  round689RateLiftedMinusTangentIsEightInputLaplacianWork ≡ true
round689RateLiftedMinusTangentIsEightInputLaplacianWorkIsTrue = refl

round689QuinticPiecesMustRemainCombinedBeforeQuarticCollapseIsTrue :
  round689QuinticPiecesMustRemainCombinedBeforeQuarticCollapse ≡ true
round689QuinticPiecesMustRemainCombinedBeforeQuarticCollapseIsTrue = refl

round689UnliftedR568BudgetControlsSignedRateLiftMinusTangentIsFalse :
  round689UnliftedR568BudgetControlsSignedRateLiftMinusTangent ≡ false
round689UnliftedR568BudgetControlsSignedRateLiftMinusTangentIsFalse = refl

round689SignedRateLiftMinusTangentSpacetimePaymentClosedIsFalse :
  round689SignedRateLiftMinusTangentSpacetimePaymentClosed ≡ false
round689SignedRateLiftMinusTangentSpacetimePaymentClosedIsFalse = refl

round689C1ClosedIsFalse :
  round689C1Closed ≡ false
round689C1ClosedIsFalse = refl

round689C2ClosedIsFalse :
  round689C2Closed ≡ false
round689C2ClosedIsFalse = refl

round689IntroducesEstimateIsFalse :
  round689IntroducesEstimate ≡ false
round689IntroducesEstimateIsFalse = refl

round689IntroducesNewClayLeafIsFalse :
  round689IntroducesNewClayLeaf ≡ false
round689IntroducesNewClayLeafIsFalse = refl

round689ClayPromotionIsFalse :
  round689ClayPromotion ≡ false
round689ClayPromotionIsFalse = refl
