{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650FiveClassSignedResidualWallRound756Exact where

------------------------------------------------------------------------
-- ROUND756 / POST-R755 CLASSWISE SIGNED-RESIDUAL ANALYTIC WALL
--
-- R744--R755 have now compiled the preferred W2 carrier down to:
--
--   0 <= integral [
--     sum_beta (
--       3 * NestedOrbit(beta)
--       - PairedDyadicTwoDifference(beta)
--     )
--     + 3 * (2 nu - delta) * d_N
--   ] dt.
--
-- Exact reductions already available:
--
--   * the complete physical triad carrier is canonical;
--   * the old R25 classifier is total and unique: LH / HL / HH / CC;
--   * the production correction must be swap-paired before three-leg energy
--     cancellation;
--   * after pairing it has exactly two actual dyadic weight differences;
--   * same-shell nonzero triads kill both production differences;
--   * in LH / HL / HH one guaranteed separated coefficient has an exact
--     shell-gap factor with gap >= Csep = 3;
--   * no Euclidean/radial coefficient substitution has been made.
--
-- What is NOT compiled:
--
--   * no sign theorem for orderedPairPower;
--   * no classwise lower bound relating the nested orbit to the paired
--     production correction;
--   * no aggregate spacetime lower bound for the R751 residual.
--
-- This file freezes that as the genuine W2 PDE wall.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Physics.Closure.NSTriadKNR650CurrentSharedWeightedWallRound736Exact as R736
import DASHI.Physics.Closure.NSTriadKNR650OrbitAlignedW2PaymentRound747Exact as R747
import DASHI.Physics.Closure.NSTriadKNR650DyadicPairedProductionDifferenceRound748Exact as R748
import DASHI.Physics.Closure.NSTriadKNR650DyadicDifferenceAlignedW2Round749Exact as R749
import DASHI.Physics.Closure.NSTriadKNR650DyadicDifferenceSupportRound750Exact as R750
import DASHI.Physics.Closure.NSTriadKNR650IntegratedDyadicDifferenceW2Round751Exact as R751
import DASHI.Physics.Closure.NSTriadKNR650DyadicDifferenceAnalyticWallRound752Exact as R752
import DASHI.Physics.Closure.NSTriadKNR650DyadicDifferenceGapFactorRound753Exact as R753
import DASHI.Physics.Closure.NSTriadKNR650DyadicDifferenceOrientedGapRound754Exact as R754
import DASHI.Physics.Closure.NSTriadKNR650FiveClassDyadicGapChannelRound755Exact as R755
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as R25

data PreferredAnalyticLeaf : Set where
  weightedPlusTerminalW1 : PreferredAnalyticLeaf
  fiveClassSignedResidualW2 : PreferredAnalyticLeaf

preferredAnalyticLeafCount : Nat
preferredAnalyticLeafCount = suc (suc zero)

leafClosed : PreferredAnalyticLeaf → Bool
leafClosed weightedPlusTerminalW1 =
  R736.round736WeightedPlusEndpointClosed
leafClosed fiveClassSignedResidualW2 =
  R751.round751ResidualNonnegativeClosed

round756ExactlyTwoPreferredAnalyticLeaves : Bool
round756ExactlyTwoPreferredAnalyticLeaves = true

round756W1StillOpen : Bool
round756W1StillOpen =
  R736.round736WeightedPlusEndpointClosed

round756W2OneSignedSpacetimeResidual : Bool
round756W2OneSignedSpacetimeResidual =
  R747.round747PreferredW2SurfaceIsOneSignedSpacetimeResidual

round756ProductionSwapPairingExact : Bool
round756ProductionSwapPairingExact =
  R748.round748DyadicProductionPairedBeforeLocalEnergyCancellation

round756ProductionTwoDifferenceCarrierExact : Bool
round756ProductionTwoDifferenceCarrierExact =
  R749.round749ProductionPartHasExactlyTwoDyadicDifferenceChannels

round756SameShellProductionCorrectionVanishes : Bool
round756SameShellProductionCorrectionVanishes =
  R750.round750TwoDifferenceProductionVanishesOnSameNonzeroShell

round756IntegratedLocalCarrierExact : Bool
round756IntegratedLocalCarrierExact =
  R751.round751IntegratedTwoDifferenceCarrierIsCanonicalR746Residual

round756DyadicGapFactorExact : Bool
round756DyadicGapFactorExact =
  R753.round753SignedDyadicDifferenceHasExactGapFactor

round756CoefficientOrientationAvailable : Bool
round756CoefficientOrientationAvailable = true

round756UsesExistingTotalUniqueFiveClassClassifier : Bool
round756UsesExistingTotalUniqueFiveClassClassifier =
  R755.round755UsesExistingTotalUniquePhysicalClassifier

round756SeparatedClassGapAtLeastThree : Bool
round756SeparatedClassGapAtLeastThree =
  R755.round755EverySeparatedGapAtLeastThree

round756PairPowerSignKnown : Bool
round756PairPowerSignKnown =
  R754.round754AssertsPairPowerSign

round756R25ClasswiseAnalyticBoundsProduced : Bool
round756R25ClasswiseAnalyticBoundsProduced =
  R25.classwiseAnalyticBoundsProduced
    R25.canonicalPhysicalFiveClassRound25Status

round756ClasswiseSignedResidualLowerBoundClosed : Bool
round756ClasswiseSignedResidualLowerBoundClosed = false

round756AggregateResidualNonnegativeClosed : Bool
round756AggregateResidualNonnegativeClosed =
  R751.round751ResidualNonnegativeClosed

round756IntroducesEstimate : Bool
round756IntroducesEstimate = false

round756ClayPromotion : Bool
round756ClayPromotion = false

round756ExactlyTwoPreferredAnalyticLeavesIsTrue :
  round756ExactlyTwoPreferredAnalyticLeaves ≡ true
round756ExactlyTwoPreferredAnalyticLeavesIsTrue = refl

round756W1StillOpenIsFalse :
  round756W1StillOpen ≡ false
round756W1StillOpenIsFalse =
  R736.round736WeightedPlusEndpointClosedIsFalse

round756W2OneSignedSpacetimeResidualIsTrue :
  round756W2OneSignedSpacetimeResidual ≡ true
round756W2OneSignedSpacetimeResidualIsTrue =
  R747.round747PreferredW2SurfaceIsOneSignedSpacetimeResidualIsTrue

round756ProductionSwapPairingExactIsTrue :
  round756ProductionSwapPairingExact ≡ true
round756ProductionSwapPairingExactIsTrue =
  R748.round748DyadicProductionPairedBeforeLocalEnergyCancellationIsTrue

round756ProductionTwoDifferenceCarrierExactIsTrue :
  round756ProductionTwoDifferenceCarrierExact ≡ true
round756ProductionTwoDifferenceCarrierExactIsTrue =
  R749.round749ProductionPartHasExactlyTwoDyadicDifferenceChannelsIsTrue

round756SameShellProductionCorrectionVanishesIsTrue :
  round756SameShellProductionCorrectionVanishes ≡ true
round756SameShellProductionCorrectionVanishesIsTrue =
  R750.round750TwoDifferenceProductionVanishesOnSameNonzeroShellIsTrue

round756IntegratedLocalCarrierExactIsTrue :
  round756IntegratedLocalCarrierExact ≡ true
round756IntegratedLocalCarrierExactIsTrue =
  R751.round751IntegratedTwoDifferenceCarrierIsCanonicalR746ResidualIsTrue

round756DyadicGapFactorExactIsTrue :
  round756DyadicGapFactorExact ≡ true
round756DyadicGapFactorExactIsTrue =
  R753.round753SignedDyadicDifferenceHasExactGapFactorIsTrue

round756CoefficientOrientationAvailableIsTrue :
  round756CoefficientOrientationAvailable ≡ true
round756CoefficientOrientationAvailableIsTrue = refl

round756UsesExistingTotalUniqueFiveClassClassifierIsTrue :
  round756UsesExistingTotalUniqueFiveClassClassifier ≡ true
round756UsesExistingTotalUniqueFiveClassClassifierIsTrue =
  R755.round755UsesExistingTotalUniquePhysicalClassifierIsTrue

round756SeparatedClassGapAtLeastThreeIsTrue :
  round756SeparatedClassGapAtLeastThree ≡ true
round756SeparatedClassGapAtLeastThreeIsTrue =
  R755.round755EverySeparatedGapAtLeastThreeIsTrue

round756PairPowerSignKnownIsFalse :
  round756PairPowerSignKnown ≡ false
round756PairPowerSignKnownIsFalse =
  R754.round754AssertsPairPowerSignIsFalse

round756R25ClasswiseAnalyticBoundsProducedIsFalse :
  round756R25ClasswiseAnalyticBoundsProduced ≡ false
round756R25ClasswiseAnalyticBoundsProducedIsFalse = refl

round756ClasswiseSignedResidualLowerBoundClosedIsFalse :
  round756ClasswiseSignedResidualLowerBoundClosed ≡ false
round756ClasswiseSignedResidualLowerBoundClosedIsFalse = refl

round756AggregateResidualNonnegativeClosedIsFalse :
  round756AggregateResidualNonnegativeClosed ≡ false
round756AggregateResidualNonnegativeClosedIsFalse =
  R751.round751ResidualNonnegativeClosedIsFalse

round756IntroducesEstimateIsFalse :
  round756IntroducesEstimate ≡ false
round756IntroducesEstimateIsFalse = refl

round756ClayPromotionIsFalse :
  round756ClayPromotion ≡ false
round756ClayPromotionIsFalse = refl
