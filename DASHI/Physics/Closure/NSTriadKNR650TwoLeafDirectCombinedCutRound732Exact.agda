{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650TwoLeafDirectCombinedCutRound732Exact where

------------------------------------------------------------------------
-- ROUND732 / NEW PARETO PERIODIC-B CUT AFTER R730
--
-- R728 exposed three proof-bearing coordinates:
--
--   A  cutoff-uniform combined/global commutator payment
--   B  combined/global commutator -> literal R406
--   C  strict-margin critical production by literal R406
--
-- R730 proves B+C compose into one strictly smaller direct theorem:
--
--   D  X_N(T) - X_N(0) + delta_N D_N(T)
--        <= IntegratedCombined_N(T),    delta_N > 0.
--
-- Therefore the Pareto terminal cut is now exactly TWO analytic leaves:
--
--   A  R723 combined/global cutoff-uniform payment;
--   D  R730 direct strict critical-growth-to-combined payment.
--
-- A + D directly imply the uniform critical barrier.  R726 + strict-margin C2
-- remain one sufficient producer factorization of D, but they are no longer
-- mandatory independent Clay-facing leaves.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Physics.Closure.NSTriadKNR650CombinedSelfExternalSpacetimeRound723Exact as R723
import DASHI.Physics.Closure.NSTriadKNR650CombinedToLiteralR406Round726Exact as R726
import DASHI.Physics.Closure.NSTriadKNR650DirectCombinedCriticalGrowthRound730Exact as R730
import DASHI.Physics.Closure.NSTriadKNR650WeightedEndpointToCombinedPaymentRound731Exact as R731

data DirectCombinedAnalyticLeaf : Set where
  combinedGlobalCutoffUniformPayment : DirectCombinedAnalyticLeaf
  directCriticalGrowthToCombined : DirectCombinedAnalyticLeaf

directCombinedAnalyticLeaves : Nat
directCombinedAnalyticLeaves = suc (suc zero)

leafClosed : DirectCombinedAnalyticLeaf → Bool
leafClosed combinedGlobalCutoffUniformPayment =
  R723.round723CombinedCutoffUniformPaymentClosed
leafClosed directCriticalGrowthToCombined =
  R730.round730DirectCombinedCriticalGrowthPaymentClosed

round732ExactlyTwoParetoAnalyticLeaves : Bool
round732ExactlyTwoParetoAnalyticLeaves = true

round732CombinedGlobalPaymentClosed : Bool
round732CombinedGlobalPaymentClosed =
  R723.round723CombinedCutoffUniformPaymentClosed

round732DirectCriticalGrowthToCombinedClosed : Bool
round732DirectCriticalGrowthToCombinedClosed =
  R730.round730DirectCombinedCriticalGrowthPaymentClosed

round732TwoLeavesBuildCriticalBarrier : Bool
round732TwoLeavesBuildCriticalBarrier =
  R730.round730DirectCombinedGrowthPlusR723BuildsCriticalBarrier

round732R726MandatoryIndependentLeaf : Bool
round732R726MandatoryIndependentLeaf =
  R730.round730SeparateR726TransportMandatoryAfterDirectRecut

round732StrictMarginC2MandatoryIndependentLeaf : Bool
round732StrictMarginC2MandatoryIndependentLeaf =
  R730.round730SeparateStrictMarginC2MandatoryAfterDirectRecut

round732R726PlusC2RemainSufficientProducerFactorization : Bool
round732R726PlusC2RemainSufficientProducerFactorization =
  R730.round730R726PlusC2BuildDirectCombinedGrowth

round732WeightedTerminalProducerForAAvailable : Bool
round732WeightedTerminalProducerForAAvailable =
  R731.round731WeightedPlusTerminalMassBuildsR723CombinedPayment

round732R726TransportClosed : Bool
round732R726TransportClosed =
  R726.round726CombinedToR406TransportClosed

round732IntroducesEstimate : Bool
round732IntroducesEstimate = false

round732ClayPromotion : Bool
round732ClayPromotion = false

round732ExactlyTwoParetoAnalyticLeavesIsTrue :
  round732ExactlyTwoParetoAnalyticLeaves ≡ true
round732ExactlyTwoParetoAnalyticLeavesIsTrue = refl

round732CombinedGlobalPaymentClosedIsFalse :
  round732CombinedGlobalPaymentClosed ≡ false
round732CombinedGlobalPaymentClosedIsFalse =
  R723.round723CombinedCutoffUniformPaymentClosedIsFalse

round732DirectCriticalGrowthToCombinedClosedIsFalse :
  round732DirectCriticalGrowthToCombinedClosed ≡ false
round732DirectCriticalGrowthToCombinedClosedIsFalse =
  R730.round730DirectCombinedCriticalGrowthPaymentClosedIsFalse

round732TwoLeavesBuildCriticalBarrierIsTrue :
  round732TwoLeavesBuildCriticalBarrier ≡ true
round732TwoLeavesBuildCriticalBarrierIsTrue =
  R730.round730DirectCombinedGrowthPlusR723BuildsCriticalBarrierIsTrue

round732R726MandatoryIndependentLeafIsFalse :
  round732R726MandatoryIndependentLeaf ≡ false
round732R726MandatoryIndependentLeafIsFalse =
  R730.round730SeparateR726TransportMandatoryAfterDirectRecutIsFalse

round732StrictMarginC2MandatoryIndependentLeafIsFalse :
  round732StrictMarginC2MandatoryIndependentLeaf ≡ false
round732StrictMarginC2MandatoryIndependentLeafIsFalse =
  R730.round730SeparateStrictMarginC2MandatoryAfterDirectRecutIsFalse

round732R726PlusC2RemainSufficientProducerFactorizationIsTrue :
  round732R726PlusC2RemainSufficientProducerFactorization ≡ true
round732R726PlusC2RemainSufficientProducerFactorizationIsTrue =
  R730.round730R726PlusC2BuildDirectCombinedGrowthIsTrue

round732WeightedTerminalProducerForAAvailableIsTrue :
  round732WeightedTerminalProducerForAAvailable ≡ true
round732WeightedTerminalProducerForAAvailableIsTrue =
  R731.round731WeightedPlusTerminalMassBuildsR723CombinedPaymentIsTrue

round732IntroducesEstimateIsFalse :
  round732IntroducesEstimate ≡ false
round732IntroducesEstimateIsFalse = refl

round732ClayPromotionIsFalse :
  round732ClayPromotion ≡ false
round732ClayPromotionIsFalse = refl
