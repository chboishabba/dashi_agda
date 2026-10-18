{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650BadCollarPairDifferenceM2PaymentRound662Exact where

------------------------------------------------------------------------
-- ROUND662 / FULL-FIBRE SIGNED PAIR DIFFERENCE -> PHYSICAL R571 M2
--
-- R660/R661 leave, on one active bad-collar output fibre, the exact signed
-- pair-difference scalar
--
--   PairDiffWork
--     = sum_{alpha<beta}
--         (lambda_alpha-lambda_beta)(w_alpha-w_beta).
--
-- Existing same-object owners already prove on the ENTIRE literal
-- physicalOutputFiber:
--
--   2 PairDiffWork = nu * CenteredDefect
--
-- and
--
--   |CenteredDefect| <= M2Budget.
--
-- Therefore, for ordinary physical 0 <= nu,
--
--   2 PairDiffWork <= nu * M2Budget.
--
-- This is a real quantitative reduction of the R661 residual.  It introduces
-- no comparable-only/P3 carrier, no fibre-cardinality tax, no sign assumption
-- on PairDiffWork, and no new PDE estimate.  The remaining local adverse term
-- is the positive self-rate work together with this explicit M2 budget.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (length)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact as D1a
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredCovarianceFactorExact as Centered
import DASHI.Physics.Closure.NSTriadKNFixedOutputViscousRateDifferenceFactorizationExact as Rate
import DASHI.Physics.Closure.NSTriadKNLiteralFixedOutputCovarianceM2PaymentExact as M2

F : C3.RealField _
F = Rational.rationalRealField

module PairDifferenceM2
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (nu : ℚ)
    (nuNonnegative : 0ℚ ≤ nu)
    (S : Helical.HelicalModeScalars F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (cutoff : Nat)
    (output : Z3.FourierMode) where

  module P = M2.LiteralFixedOutputCovarianceM2
    {E = E} {I = I} S velocity cutoff output

  items = Output.physicalOutputFiber cutoff output
  value = D1a.mixedProductCell S velocity
  mixed = R224.foldVector value items
  work = Pair.cellWork mixed value
  rate = Pair.cellRate (Centered.modalViscousRate nu I)

  pairDifference : ℚ
  pairDifference =
    Pair.pairDifferenceWorkSum rate work items

  centeredDefect : ℚ
  centeredDefect =
    Centered.centeredPairDifferenceWorkSum E work items

  exactPhysicalFactor :
    Rate.two * pairDifference
    ≡ nu * centeredDefect
  exactPhysicalFactor =
    Centered.literalFixedOutputCenteredCovarianceFactor
      E I nu work cutoff output

  centeredDefectBelowM2 :
    centeredDefect ≤ P.totalM2Budget items
  centeredDefectBelowM2 =
    P.literalFixedOutputCenteredCovarianceBelowM2

  scaledCenteredDefectBelowM2 :
    nu * centeredDefect
    ≤ nu * P.totalM2Budget items
  scaledCenteredDefectBelowM2 =
    let instance nuNN = nonNegative nuNonnegative
    in
    ℚP.*-monoˡ-≤-nonNeg nu centeredDefectBelowM2

  signedPairDifferenceBelowPhysicalM2 :
    Rate.two * pairDifference
    ≤ nu * P.totalM2Budget items
  signedPairDifferenceBelowPhysicalM2 =
    subst
      (λ left → left ≤ nu * P.totalM2Budget items)
      (sym exactPhysicalFactor)
      scaledCenteredDefectBelowM2

  selfRateWork : ℚ
  selfRateWork =
    Pair.rateSum rate items * Work.coherentWork mixed mixed

  rateSelfPlusPairDifference : ℚ
  rateSelfPlusPairDifference =
    selfRateWork + pairDifference

  doubledResidualBelowSelfPlusM2 :
    Rate.two * rateSelfPlusPairDifference
    ≤ Rate.two * selfRateWork + nu * P.totalM2Budget items
  doubledResidualBelowSelfPlusM2 =
    let
      expanded :
        Rate.two * rateSelfPlusPairDifference
        ≡ Rate.two * selfRateWork + Rate.two * pairDifference
      expanded =
        solve
          ( selfRateWork
          ∷ pairDifference
          ∷ [])

      bounded :
        Rate.two * selfRateWork + Rate.two * pairDifference
        ≤ Rate.two * selfRateWork + nu * P.totalM2Budget items
      bounded =
        ℚP.+-mono-≤ ℚP.≤-refl signedPairDifferenceBelowPhysicalM2
    in
    subst
      (λ left →
        left ≤ Rate.two * selfRateWork + nu * P.totalM2Budget items)
      (sym expanded)
      bounded

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round662PhysicalPairDifferenceFactorClosed : Bool
round662PhysicalPairDifferenceFactorClosed = true

round662FullFibreSignedPairDifferenceM2PaymentClosed : Bool
round662FullFibreSignedPairDifferenceM2PaymentClosed = true

round662PairDifferenceM2AddsCardinalityTax : Bool
round662PairDifferenceM2AddsCardinalityTax = false

round662RequiresComparableOnlyP3Carrier : Bool
round662RequiresComparableOnlyP3Carrier = false

round662R661ResidualReducedToSelfRatePlusM2 : Bool
round662R661ResidualReducedToSelfRatePlusM2 = true

round662PaysR661SelfRateTerm : Bool
round662PaysR661SelfRateTerm = false

round662CutoffUniformM2AggregationClosed : Bool
round662CutoffUniformM2AggregationClosed = false

round662IntroducesNewClayLeaf : Bool
round662IntroducesNewClayLeaf = false

round662C2Closed : Bool
round662C2Closed = false

round662ClayPromotion : Bool
round662ClayPromotion = false

round662PhysicalPairDifferenceFactorClosedIsTrue :
  round662PhysicalPairDifferenceFactorClosed ≡ true
round662PhysicalPairDifferenceFactorClosedIsTrue = refl

round662FullFibreSignedPairDifferenceM2PaymentClosedIsTrue :
  round662FullFibreSignedPairDifferenceM2PaymentClosed ≡ true
round662FullFibreSignedPairDifferenceM2PaymentClosedIsTrue = refl

round662PairDifferenceM2AddsCardinalityTaxIsFalse :
  round662PairDifferenceM2AddsCardinalityTax ≡ false
round662PairDifferenceM2AddsCardinalityTaxIsFalse = refl

round662RequiresComparableOnlyP3CarrierIsFalse :
  round662RequiresComparableOnlyP3Carrier ≡ false
round662RequiresComparableOnlyP3CarrierIsFalse = refl

round662R661ResidualReducedToSelfRatePlusM2IsTrue :
  round662R661ResidualReducedToSelfRatePlusM2 ≡ true
round662R661ResidualReducedToSelfRatePlusM2IsTrue = refl

round662PaysR661SelfRateTermIsFalse :
  round662PaysR661SelfRateTerm ≡ false
round662PaysR661SelfRateTermIsFalse = refl

round662CutoffUniformM2AggregationClosedIsFalse :
  round662CutoffUniformM2AggregationClosed ≡ false
round662CutoffUniformM2AggregationClosedIsFalse = refl

round662IntroducesNewClayLeafIsFalse :
  round662IntroducesNewClayLeaf ≡ false
round662IntroducesNewClayLeafIsFalse = refl

round662C2ClosedIsFalse :
  round662C2Closed ≡ false
round662C2ClosedIsFalse = refl

round662ClayPromotionIsFalse :
  round662ClayPromotion ≡ false
round662ClayPromotionIsFalse = refl
