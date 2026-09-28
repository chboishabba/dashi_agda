{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650DyadicDifferenceAnalyticWallRound752Exact where

------------------------------------------------------------------------
-- ROUND752 / CURRENT PERIODIC-B ANALYTIC WALL AFTER COMMON-CARRIER ALIGNMENT
--
-- R744-R751 sharpen W2 without adding an estimate:
--
--   * literal critical production is on the complete zero-masked physical
--     triad carrier;
--   * production and R723 combined residue share the same outer cyclic carrier;
--   * W2 is exactly nonnegativity of one signed spacetime residual;
--   * the production subtraction must first be paired with the swap mate;
--   * after that pairing it is EXACTLY two actual dyadic multiplier-difference
--     channels;
--   * those two channels vanish on same-shell nonzero triads.
--
-- Thus the preferred W2 analytic object is now
--
--   0 <= integral [
--     sum_beta (
--       3 * NestedOrbit(beta)
--       - PairedDyadicTwoDifference(beta)
--     )
--     + 3 * (2 nu - delta) * d_N
--   ] dt.
--
-- No exhaustive new shell partition is asserted here: the repository's
-- absolute six-way geometry partition is still explicitly open.  R750 is
-- used only as the exact one-way same-shell vanishing theorem it actually is.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Physics.Closure.NSTriadKNR650CurrentSharedWeightedWallRound736Exact as R736
import DASHI.Physics.Closure.NSTriadKNR650PostDerivativeAnalyticWallRound743Exact as R743
import DASHI.Physics.Closure.NSTriadKNR650CriticalProductionIncidenceCarrierRound744Exact as R744
import DASHI.Physics.Closure.NSTriadKNR650OrbitAlignedW2ResidualRound745Exact as R745
import DASHI.Physics.Closure.NSTriadKNR650IntegratedOrbitAlignedW2ResidualRound746Exact as R746
import DASHI.Physics.Closure.NSTriadKNR650OrbitAlignedW2PaymentRound747Exact as R747
import DASHI.Physics.Closure.NSTriadKNR650DyadicPairedProductionDifferenceRound748Exact as R748
import DASHI.Physics.Closure.NSTriadKNR650DyadicDifferenceAlignedW2Round749Exact as R749
import DASHI.Physics.Closure.NSTriadKNR650DyadicDifferenceSupportRound750Exact as R750
import DASHI.Physics.Closure.NSTriadKNR650IntegratedDyadicDifferenceW2Round751Exact as R751
import DASHI.Physics.Closure.NSTriadKNExactDyadicShellGeometry as ShellGeometry

data CurrentAnalyticLeaf : Set where
  weightedPlusTerminalW1 : CurrentAnalyticLeaf
  dyadicDifferenceResidualW2 : CurrentAnalyticLeaf

currentAnalyticLeafCount : Nat
currentAnalyticLeafCount = suc (suc zero)

leafClosed : CurrentAnalyticLeaf → Bool
leafClosed weightedPlusTerminalW1 =
  R736.round736WeightedPlusEndpointClosed
leafClosed dyadicDifferenceResidualW2 =
  R751.round751ResidualNonnegativeClosed

round752ExactlyTwoPreferredAnalyticLeaves : Bool
round752ExactlyTwoPreferredAnalyticLeaves = true

round752W1StillWeightedPlusTerminalPayment : Bool
round752W1StillWeightedPlusTerminalPayment = true

round752W2IsOneSignedSpacetimeResidual : Bool
round752W2IsOneSignedSpacetimeResidual =
  R747.round747PreferredW2SurfaceIsOneSignedSpacetimeResidual

round752CriticalProductionUsesCompletePhysicalCarrier : Bool
round752CriticalProductionUsesCompletePhysicalCarrier =
  R744.round744CriticalProductionOnCompletePhysicalIncidenceCarrier

round752W2NonlinearTermsShareOneOuterCarrier : Bool
round752W2NonlinearTermsShareOneOuterCarrier =
  R745.round745ProductionAndCombinedShareCompleteOuterCarrier

round752IntegratedResidualIdentityClosed : Bool
round752IntegratedResidualIdentityClosed =
  R746.round746IntegratedOrbitAlignedResidualExact

round752ProductionMustBeSwapPairedBeforeThreeLegCancellation : Bool
round752ProductionMustBeSwapPairedBeforeThreeLegCancellation =
  R748.round748DyadicProductionPairedBeforeLocalEnergyCancellation

round752ProductionHasTwoActualDyadicDifferenceChannels : Bool
round752ProductionHasTwoActualDyadicDifferenceChannels =
  R749.round749ProductionPartHasExactlyTwoDyadicDifferenceChannels

round752SameShellNonzeroProductionCorrectionVanishes : Bool
round752SameShellNonzeroProductionCorrectionVanishes =
  R750.round750TwoDifferenceProductionVanishesOnSameNonzeroShell

round752IntegratedTwoDifferenceCarrierIsCanonicalW2Residual : Bool
round752IntegratedTwoDifferenceCarrierIsCanonicalW2Residual =
  R751.round751IntegratedTwoDifferenceCarrierIsCanonicalR746Residual

round752FullNewShellPartitionClaimed : Bool
round752FullNewShellPartitionClaimed = false

round752RepositoryAbsoluteGeometryPartitionAlreadyClosed : Bool
round752RepositoryAbsoluteGeometryPartitionAlreadyClosed =
  ShellGeometry.fullRepositoryGeometryPartitionClosed

round752W1Closed : Bool
round752W1Closed =
  R736.round736WeightedPlusEndpointClosed

round752W2ResidualNonnegativeClosed : Bool
round752W2ResidualNonnegativeClosed =
  R751.round751ResidualNonnegativeClosed

round752IntroducesEstimate : Bool
round752IntroducesEstimate = false

round752ClayPromotion : Bool
round752ClayPromotion = false

round752ExactlyTwoPreferredAnalyticLeavesIsTrue :
  round752ExactlyTwoPreferredAnalyticLeaves ≡ true
round752ExactlyTwoPreferredAnalyticLeavesIsTrue = refl

round752W1StillWeightedPlusTerminalPaymentIsTrue :
  round752W1StillWeightedPlusTerminalPayment ≡ true
round752W1StillWeightedPlusTerminalPaymentIsTrue = refl

round752W2IsOneSignedSpacetimeResidualIsTrue :
  round752W2IsOneSignedSpacetimeResidual ≡ true
round752W2IsOneSignedSpacetimeResidualIsTrue =
  R747.round747PreferredW2SurfaceIsOneSignedSpacetimeResidualIsTrue

round752CriticalProductionUsesCompletePhysicalCarrierIsTrue :
  round752CriticalProductionUsesCompletePhysicalCarrier ≡ true
round752CriticalProductionUsesCompletePhysicalCarrierIsTrue =
  R744.round744CriticalProductionOnCompletePhysicalIncidenceCarrierIsTrue

round752W2NonlinearTermsShareOneOuterCarrierIsTrue :
  round752W2NonlinearTermsShareOneOuterCarrier ≡ true
round752W2NonlinearTermsShareOneOuterCarrierIsTrue =
  R745.round745ProductionAndCombinedShareCompleteOuterCarrierIsTrue

round752IntegratedResidualIdentityClosedIsTrue :
  round752IntegratedResidualIdentityClosed ≡ true
round752IntegratedResidualIdentityClosedIsTrue =
  R746.round746IntegratedOrbitAlignedResidualExactIsTrue

round752ProductionMustBeSwapPairedBeforeThreeLegCancellationIsTrue :
  round752ProductionMustBeSwapPairedBeforeThreeLegCancellation ≡ true
round752ProductionMustBeSwapPairedBeforeThreeLegCancellationIsTrue =
  R748.round748DyadicProductionPairedBeforeLocalEnergyCancellationIsTrue

round752ProductionHasTwoActualDyadicDifferenceChannelsIsTrue :
  round752ProductionHasTwoActualDyadicDifferenceChannels ≡ true
round752ProductionHasTwoActualDyadicDifferenceChannelsIsTrue =
  R749.round749ProductionPartHasExactlyTwoDyadicDifferenceChannelsIsTrue

round752SameShellNonzeroProductionCorrectionVanishesIsTrue :
  round752SameShellNonzeroProductionCorrectionVanishes ≡ true
round752SameShellNonzeroProductionCorrectionVanishesIsTrue =
  R750.round750TwoDifferenceProductionVanishesOnSameNonzeroShellIsTrue

round752IntegratedTwoDifferenceCarrierIsCanonicalW2ResidualIsTrue :
  round752IntegratedTwoDifferenceCarrierIsCanonicalW2Residual ≡ true
round752IntegratedTwoDifferenceCarrierIsCanonicalW2ResidualIsTrue =
  R751.round751IntegratedTwoDifferenceCarrierIsCanonicalR746ResidualIsTrue

round752FullNewShellPartitionClaimedIsFalse :
  round752FullNewShellPartitionClaimed ≡ false
round752FullNewShellPartitionClaimedIsFalse = refl

round752RepositoryAbsoluteGeometryPartitionAlreadyClosedIsFalse :
  round752RepositoryAbsoluteGeometryPartitionAlreadyClosed ≡ false
round752RepositoryAbsoluteGeometryPartitionAlreadyClosedIsFalse =
  ShellGeometry.fullRepositoryGeometryPartitionClosedIsFalse

round752W1ClosedIsFalse :
  round752W1Closed ≡ false
round752W1ClosedIsFalse =
  R736.round736WeightedPlusEndpointClosedIsFalse

round752W2ResidualNonnegativeClosedIsFalse :
  round752W2ResidualNonnegativeClosed ≡ false
round752W2ResidualNonnegativeClosedIsFalse =
  R751.round751ResidualNonnegativeClosedIsFalse

round752IntroducesEstimateIsFalse :
  round752IntroducesEstimate ≡ false
round752IntroducesEstimateIsFalse = refl

round752ClayPromotionIsFalse :
  round752ClayPromotion ≡ false
round752ClayPromotionIsFalse = refl
