module DASHI.Culture.AmyEskridgeLiTorrSourceConstitutiveCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Culture.AmyEskridgeLiTorrGeometryFactorCrossPollinationExact as E
import DASHI.Physics.ExoticGravity.SuperconductingSourceVsConstitutiveEnhancementBidiExact as S

------------------------------------------------------------------------
-- ESKRIDGE / LI-TORR SOURCE-vs-CONSTITUTIVE CROSS-POLLINATION
------------------------------------------------------------------------

record EskridgeSourceConstitutiveBoundary : Set where
  constructor eskridge-source-constitutive-boundary
  field
    liTorrFamilyIsRelevantCandidate : Bool
    liTorrFamilyIsRelevantCandidateIsTrue :
      liTorrFamilyIsRelevantCandidate ≡ true

    phaseDependentFieldImpliesNewGravityCoupling : Bool
    phaseDependentFieldImpliesNewGravityCouplingIsFalse :
      phaseDependentFieldImpliesNewGravityCoupling ≡ false

    changedMassCurrentMustBeEstimatedFirst : Bool
    changedMassCurrentMustBeEstimatedFirstIsTrue :
      changedMassCurrentMustBeEstimatedFirst ≡ true

    constitutivePromotionRequiresResidualAfterSourceCorrection : Bool
    constitutivePromotionRequiresResidualAfterSourceCorrectionIsTrue :
      constitutivePromotionRequiresResidualAfterSourceCorrection ≡ true

canonicalEskridgeSourceConstitutiveBoundary : EskridgeSourceConstitutiveBoundary
canonicalEskridgeSourceConstitutiveBoundary =
  eskridge-source-constitutive-boundary true refl false refl true refl true refl

------------------------------------------------------------------------
-- Reuse the physics frontier.
------------------------------------------------------------------------

sourceConstitutiveFrontier : S.EnhancementLeaf
sourceConstitutiveFrontier = S.currentFirstOpenEnhancementLeaf

------------------------------------------------------------------------
-- Experimental interpretation.
------------------------------------------------------------------------

record EskridgeSourceConstitutiveExperiment : Set where
  constructor eskridge-source-constitutive-experiment
  field
    measureSourceCurrentAboveTc : Bool
    measureSourceCurrentAboveTcIsTrue : measureSourceCurrentAboveTc ≡ true

    measureSourceCurrentBelowTc : Bool
    measureSourceCurrentBelowTcIsTrue : measureSourceCurrentBelowTc ≡ true

    measureExternalGravityChannelAboveTc : Bool
    measureExternalGravityChannelAboveTcIsTrue :
      measureExternalGravityChannelAboveTc ≡ true

    measureExternalGravityChannelBelowTc : Bool
    measureExternalGravityChannelBelowTcIsTrue :
      measureExternalGravityChannelBelowTc ≡ true

    compareMeasuredFieldToGRUsingMeasuredSource : Bool
    compareMeasuredFieldToGRUsingMeasuredSourceIsTrue :
      compareMeasuredFieldToGRUsingMeasuredSource ≡ true

canonicalEskridgeSourceConstitutiveExperiment : EskridgeSourceConstitutiveExperiment
canonicalEskridgeSourceConstitutiveExperiment =
  eskridge-source-constitutive-experiment
    true refl true refl true refl true refl true refl
