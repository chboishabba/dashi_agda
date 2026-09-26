{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650CurrentSharedWeightedWallRound736Exact where

------------------------------------------------------------------------
-- ROUND736 / CURRENT PREFERRED ANALYTIC WALL
--
-- R732 proves the Pareto theorem count is two.
-- R733 identifies the endpoint E_M exactly with canonical Q_+-.
-- R734 rewrites direct leaf D onto the weighted/input-Laplacian carrier.
-- R735 puts BOTH leaves on that same signed quartic carrier.
--
-- The current preferred leaves are therefore:
--
--   W1  cutoff-uniform signed weighted-plus-terminal payment
--
--         W_N(T) + Q_+-,N(T) <= B(T);
--
--   W2  positive-margin augmented-critical weighted payment
--
--         [X_N(T) - 12 Q_+-,N(T)]
--           - [X_N(0) - 12 Q_+-,N(0)]
--           + delta_N D_N(T)
--         <= 12 W_N(T),          delta_N > 0.
--
-- W1 + W2 compile to the ordinary critical barrier.
--
-- Exact alternative presentations remain available:
--
--   W1 -> R723 combined/global commutator payment;
--   W2 <-> R730 direct critical-growth-to-combined;
--   R726 + strict-margin R406 C2 -> W2 via R730/R734.
--
-- None of those alternative coordinates adds a third mandatory theorem.
--
-- The endpoint shortcut through R241 is circular here: R241's Q_+- payment
-- assumes the uniform critical barrier that W1+W2 are intended to prove.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Physics.Closure.NSTriadKNR650SharedWeightedQuarticCutRound735Exact as R735
import DASHI.Physics.Closure.NSTriadKNR650AugmentedCriticalWeightedNormalFormRound734Exact as R734
import DASHI.Physics.Closure.NSTriadKNR650TerminalMixedMassQPlusMinusRound733Exact as R733
import DASHI.Physics.Closure.NSTriadKNR650TwoLeafDirectCombinedCutRound732Exact as R732
import DASHI.Physics.Closure.NSTriadKNR650WeightedEndpointToCombinedPaymentRound731Exact as R731
import DASHI.Physics.Closure.NSTriadKNR650DirectCombinedCriticalGrowthRound730Exact as R730
import DASHI.Physics.Closure.NSTriadKNR650CombinedToLiteralR406Round726Exact as R726
import DASHI.Physics.Closure.NSTriadKNR650RateKernelInputLaplacianCollapseRound684Exact as R684

data CurrentSharedWeightedLeaf : Set where
  weightedPlusQPlusMinusEndpoint : CurrentSharedWeightedLeaf
  augmentedCriticalWeightedPayment : CurrentSharedWeightedLeaf

currentSharedWeightedLeafCount : Nat
currentSharedWeightedLeafCount = suc (suc zero)

leafClosed : CurrentSharedWeightedLeaf → Bool
leafClosed weightedPlusQPlusMinusEndpoint =
  R735.round735WeightedPlusTerminalPaymentClosed
leafClosed augmentedCriticalWeightedPayment =
  R735.round735AugmentedCriticalWeightedPaymentClosed

round736ExactlyTwoPreferredAnalyticLeaves : Bool
round736ExactlyTwoPreferredAnalyticLeaves = true

round736BothLeavesUseSameWeightedCarrier : Bool
round736BothLeavesUseSameWeightedCarrier =
  R735.round735PreferredCutUsesOneSharedWeightedCarrier

round736QuinticCommutatorAbsentFromPreferredTargets : Bool
round736QuinticCommutatorAbsentFromPreferredTargets =
  R735.round735QuinticCommutatorAbsentFromBothPreferredLeaves

round736WeightedCarrierIsInputLaplacianWork : Bool
round736WeightedCarrierIsInputLaplacianWork =
  R684.round684PhysicalRateKernelIsInputLaplacianWork

round736EndpointIsCanonicalQPlusMinus : Bool
round736EndpointIsCanonicalQPlusMinus =
  R733.round733R691EndpointIsCanonicalR227QPlusMinus

round736WeightedPlusEndpointClosed : Bool
round736WeightedPlusEndpointClosed =
  R735.round735WeightedPlusTerminalPaymentClosed

round736AugmentedCriticalWeightedClosed : Bool
round736AugmentedCriticalWeightedClosed =
  R734.round734AugmentedWeightedPaymentClosed

round736TwoLeavesBuildCriticalBarrier : Bool
round736TwoLeavesBuildCriticalBarrier =
  R735.round735TwoSharedWeightedLeavesBuildBarrier

round736R732TwoLeafCountPreserved : Bool
round736R732TwoLeafCountPreserved =
  R732.round732ExactlyTwoParetoAnalyticLeaves

round736R726IndependentLeafRequired : Bool
round736R726IndependentLeafRequired =
  R732.round732R726MandatoryIndependentLeaf

round736StrictMarginR406IndependentLeafRequired : Bool
round736StrictMarginR406IndependentLeafRequired =
  R732.round732StrictMarginC2MandatoryIndependentLeaf

round736R726PlusC2RemainSufficientProducer : Bool
round736R726PlusC2RemainSufficientProducer =
  R730.round730R726PlusC2BuildDirectCombinedGrowth

round736BarrierDependentQPlusMinusShortcutAdmissible : Bool
round736BarrierDependentQPlusMinusShortcutAdmissible =
  R733.round733UsingCriticalBarrierToPayAEndpointIsNoncircular

round736IntroducesEstimate : Bool
round736IntroducesEstimate = false

round736ClayPromotion : Bool
round736ClayPromotion = false

round736ExactlyTwoPreferredAnalyticLeavesIsTrue :
  round736ExactlyTwoPreferredAnalyticLeaves ≡ true
round736ExactlyTwoPreferredAnalyticLeavesIsTrue = refl

round736BothLeavesUseSameWeightedCarrierIsTrue :
  round736BothLeavesUseSameWeightedCarrier ≡ true
round736BothLeavesUseSameWeightedCarrierIsTrue =
  R735.round735PreferredCutUsesOneSharedWeightedCarrierIsTrue

round736QuinticCommutatorAbsentFromPreferredTargetsIsTrue :
  round736QuinticCommutatorAbsentFromPreferredTargets ≡ true
round736QuinticCommutatorAbsentFromPreferredTargetsIsTrue =
  R735.round735QuinticCommutatorAbsentFromBothPreferredLeavesIsTrue

round736WeightedCarrierIsInputLaplacianWorkIsTrue :
  round736WeightedCarrierIsInputLaplacianWork ≡ true
round736WeightedCarrierIsInputLaplacianWorkIsTrue =
  R684.round684PhysicalRateKernelIsInputLaplacianWorkIsTrue

round736EndpointIsCanonicalQPlusMinusIsTrue :
  round736EndpointIsCanonicalQPlusMinus ≡ true
round736EndpointIsCanonicalQPlusMinusIsTrue =
  R733.round733R691EndpointIsCanonicalR227QPlusMinusIsTrue

round736WeightedPlusEndpointClosedIsFalse :
  round736WeightedPlusEndpointClosed ≡ false
round736WeightedPlusEndpointClosedIsFalse =
  R735.round735WeightedPlusTerminalPaymentClosedIsFalse

round736AugmentedCriticalWeightedClosedIsFalse :
  round736AugmentedCriticalWeightedClosed ≡ false
round736AugmentedCriticalWeightedClosedIsFalse =
  R734.round734AugmentedWeightedPaymentClosedIsFalse

round736TwoLeavesBuildCriticalBarrierIsTrue :
  round736TwoLeavesBuildCriticalBarrier ≡ true
round736TwoLeavesBuildCriticalBarrierIsTrue =
  R735.round735TwoSharedWeightedLeavesBuildBarrierIsTrue

round736R732TwoLeafCountPreservedIsTrue :
  round736R732TwoLeafCountPreserved ≡ true
round736R732TwoLeafCountPreservedIsTrue =
  R732.round732ExactlyTwoParetoAnalyticLeavesIsTrue

round736R726IndependentLeafRequiredIsFalse :
  round736R726IndependentLeafRequired ≡ false
round736R726IndependentLeafRequiredIsFalse =
  R732.round732R726MandatoryIndependentLeafIsFalse

round736StrictMarginR406IndependentLeafRequiredIsFalse :
  round736StrictMarginR406IndependentLeafRequired ≡ false
round736StrictMarginR406IndependentLeafRequiredIsFalse =
  R732.round732StrictMarginC2MandatoryIndependentLeafIsFalse

round736R726PlusC2RemainSufficientProducerIsTrue :
  round736R726PlusC2RemainSufficientProducer ≡ true
round736R726PlusC2RemainSufficientProducerIsTrue =
  R730.round730R726PlusC2BuildDirectCombinedGrowthIsTrue

round736BarrierDependentQPlusMinusShortcutAdmissibleIsFalse :
  round736BarrierDependentQPlusMinusShortcutAdmissible ≡ false
round736BarrierDependentQPlusMinusShortcutAdmissibleIsFalse =
  R733.round733UsingCriticalBarrierToPayAEndpointIsNoncircularIsFalse

round736IntroducesEstimateIsFalse :
  round736IntroducesEstimate ≡ false
round736IntroducesEstimateIsFalse = refl

round736ClayPromotionIsFalse :
  round736ClayPromotion ≡ false
round736ClayPromotionIsFalse = refl
