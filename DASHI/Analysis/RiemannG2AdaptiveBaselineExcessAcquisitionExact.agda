module DASHI.Analysis.RiemannG2AdaptiveBaselineExcessAcquisitionExact where

------------------------------------------------------------------------
-- ADAPTIVE BASELINE-EXCESS ACQUISITION FRONTIER
--
-- The recovered 8889 cluster source gives a margin
--
--   M(a,g) = (sqrt(2)/2) * a^2 * secondMoment(g)
--
-- above the shared baseline.  The far remainder can be made to live on the
-- same a^2-scale by increasing the cutoff as |a| decreases.
--
-- That improvement has a real analytic cost: increasing J enlarges the finite
-- nearOffFinset whose SIGNED response must be controlled.  Therefore the live
-- near theorem is not a pointwise per-cell O(a^2/t^2) estimate.  It is a
-- uniform cancellation/enclosure theorem for the adaptively expanding finite
-- near core, coordinated with the far and Gamma errors so their combined
-- excess stays strictly below M(a,g).
------------------------------------------------------------------------

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

record AdaptiveBaselineExcessAcquisition : Set₁ where
  field
    Scalar Cutoff : Set
    _≤_ _<_ : Scalar → Scalar → Set
    add : Scalar → Scalar → Scalar

    horizontalDisplacement : Scalar
    targetOrdinate : Scalar
    chosenCutoff : Cutoff

    baselineCluster : Scalar
    clusterMargin : Scalar

    finiteNearBudget : Scalar
    farBudget : Scalar
    gammaBudget : Scalar

    offGammaExcess : Scalar

    chosenCutoffTracksHorizontalDisplacement : Set
    chosenCutoffTracksHorizontalDisplacementReceipt :
      chosenCutoffTracksHorizontalDisplacement

    quarterPeriodCrossedAtChosenCutoff : Set
    quarterPeriodCrossedAtChosenCutoffReceipt :
      quarterPeriodCrossedAtChosenCutoff

    finiteNearPlusFarPlusGammaBelowBaselinePlusExcess :
      _≤_
        (add (add finiteNearBudget farBudget) gammaBudget)
        (add baselineCluster offGammaExcess)

    excessFitsRecoveredClusterMargin :
      _<_ offGammaExcess clusterMargin

    sameObjectsAsFinalPoleQuotientConsumer : Set
    sameObjectsAsFinalPoleQuotientConsumerReceipt :
      sameObjectsAsFinalPoleQuotientConsumer

    acquisitionReference : String

open AdaptiveBaselineExcessAcquisition public

record AdaptiveBaselineExcessBoundary : Set where
  constructor adaptive-baseline-excess-boundary
  field
    farAccuracyCanTrackHorizontalSquare : Bool
    shrinkingHorizontalDisplacementForcesFixedFiniteNearCarrier : Bool
    adaptiveCutoffMayEnlargeFiniteNearCarrier : Bool
    nearLeafIsUniformSignedFiniteCoreCancellation : Bool
    gammaLeafIsSharpSameTaperRepair : Bool
    recoveredClusterLowerIsFreshAnalysis : Bool
    combinedExcessStrictnessStillOpen : Bool
    rhDerivedHere : Bool

open AdaptiveBaselineExcessBoundary public

canonicalAdaptiveBaselineExcessBoundary : AdaptiveBaselineExcessBoundary
canonicalAdaptiveBaselineExcessBoundary =
  adaptive-baseline-excess-boundary
    true
    false
    true
    true
    true
    false
    true
    false
