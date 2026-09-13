module DASHI.Reasoning.CrossCulturalCompassionAccountabilityRegression where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Reasoning.CrossCulturalCompassionAccountabilityExact as Cross

sourceCountRegression : Cross.crossCulturalCompassionSourceCount ≡ 2
sourceCountRegression = refl

sourceAtlasNonPromotingRegression :
  Attr.atlasCreatesAuthority Cross.crossCulturalCompassionSourceAtlas ≡ false
sourceAtlasNonPromotingRegression =
  Cross.crossCulturalCompassionAtlasDoesNotCreateAuthority

individualistAdviceNotUniversalRegression :
  Cross.BoundaryAdviceFirewall.westernIndividualistAdviceUniversallyApplicable
    Cross.canonicalBoundaryAdviceFirewall ≡ false
individualistAdviceNotUniversalRegression = refl

familyHarmonyNotUniversalOverrideRegression :
  Cross.BoundaryAdviceFirewall.familyHarmonyUniversallyOverridesAutonomy
    Cross.canonicalBoundaryAdviceFirewall ≡ false
familyHarmonyNotUniversalOverrideRegression = refl

culturalNormNotPreferenceDeterminismRegression :
  Cross.BoundaryAdviceFirewall.culturalNormDeterminesIndividualPreference
    Cross.canonicalBoundaryAdviceFirewall ≡ false
culturalNormNotPreferenceDeterminismRegression = refl

dependencyNotConsentRegression :
  Cross.BoundaryAdviceFirewall.dependencyImpliesConsent
    Cross.canonicalBoundaryAdviceFirewall ≡ false
dependencyNotConsentRegression = refl

relationshipPreservationDoesNotDeleteBoundaryRegression :
  Cross.BoundaryAdviceFirewall.preservingRelationshipImpliesNoBoundary
    Cross.canonicalBoundaryAdviceFirewall ≡ false
relationshipPreservationDoesNotDeleteBoundaryRegression = refl

compassionNotAccountabilityErasureRegression :
  Cross.responsibilityErasedByCompassion
    Cross.canonicalCompassionAccountabilityState ≡ false
compassionNotAccountabilityErasureRegression =
  Cross.compassionDoesNotEraseAccountability

explanationNotAccountabilityErasureRegression :
  Cross.responsibilityErasedByExplanation
    Cross.canonicalCompassionAccountabilityState ≡ false
explanationNotAccountabilityErasureRegression =
  Cross.explanationDoesNotEraseAccountability

compassionNotReconciliationRegression :
  Cross.reconciliationRequired Cross.canonicalCompassionAccountabilityState ≡ false
compassionNotReconciliationRegression =
  Cross.compassionDoesNotRequireReconciliation

audiencePressureNotTruthRegression :
  Cross.audienceJudgementTrue Cross.canonicalAudiencePressureBoundary ≡ false
audiencePressureNotTruthRegression = Cross.audienceSalienceDoesNotCreateTruth

audiencePressureNotAuthorityRegression :
  Cross.audienceJudgementAuthoritative Cross.canonicalAudiencePressureBoundary ≡ false
audiencePressureNotAuthorityRegression = Cross.audienceSalienceDoesNotCreateAuthority

practitionerLabelNotDiagnosisRegression :
  Cross.PractitionerLabelBoundary.labelDiagnosesNamedPerson
    Cross.canonicalEmotionallyImmatureLabelBoundary ≡ false
practitionerLabelNotDiagnosisRegression = Cross.emotionallyImmatureLabelDoesNotDiagnose

practitionerLabelNotMisconductProofRegression :
  Cross.PractitionerLabelBoundary.labelProvesMisconduct
    Cross.canonicalEmotionallyImmatureLabelBoundary ≡ false
practitionerLabelNotMisconductProofRegression =
  Cross.emotionallyImmatureLabelDoesNotProveMisconduct

careNotComplaintErasureRegression :
  Cross.CareComplaintBoundary.careErasesComplaint
    Cross.canonicalCareComplaintBoundary ≡ false
careNotComplaintErasureRegression = Cross.careDoesNotEraseComplaint

gratitudeNotConsentWaiverRegression :
  Cross.CareComplaintBoundary.gratitudeWaivesConsent
    Cross.canonicalCareComplaintBoundary ≡ false
gratitudeNotConsentWaiverRegression = Cross.gratitudeDoesNotWaiveConsent

compassionNotBoundaryWaiverRegression :
  Cross.CareComplaintBoundary.compassionWaivesBoundary
    Cross.canonicalCareComplaintBoundary ≡ false
compassionNotBoundaryWaiverRegression = Cross.compassionDoesNotWaiveBoundary

------------------------------------------------------------------------
-- Positive construction: compassion, belonging, relationship continuity,
-- accountability, consent and bounded access must be jointly inhabitable.
------------------------------------------------------------------------

positiveWitnessKeepsPerspectiveTakingRegression :
  Cross.CompassionWithoutSelfErasure.perspectiveTakingRetained
    Cross.canonicalCompassionWithoutSelfErasure ≡ true
positiveWitnessKeepsPerspectiveTakingRegression = refl

positiveWitnessKeepsRelationshipRegression :
  Cross.CompassionWithoutSelfErasure.continuedRelationshipPossible
    Cross.canonicalCompassionWithoutSelfErasure ≡ true
positiveWitnessKeepsRelationshipRegression = refl

positiveWitnessKeepsBelongingRegression :
  Cross.CompassionWithoutSelfErasure.culturalBelongingPreserved
    Cross.canonicalCompassionWithoutSelfErasure ≡ true
positiveWitnessKeepsBelongingRegression = refl

positiveWitnessKeepsAccountabilityRegression :
  Cross.CompassionWithoutSelfErasure.accountabilityPreserved
    Cross.canonicalCompassionWithoutSelfErasure ≡ true
positiveWitnessKeepsAccountabilityRegression = refl

positiveWitnessKeepsBoundedAccessRegression :
  Cross.CompassionWithoutSelfErasure.boundedAccessPreserved
    Cross.canonicalCompassionWithoutSelfErasure ≡ true
positiveWitnessKeepsBoundedAccessRegression = refl

positiveWitnessKeepsConsentRegression :
  Cross.CompassionWithoutSelfErasure.consentPreserved
    Cross.canonicalCompassionWithoutSelfErasure ≡ true
positiveWitnessKeepsConsentRegression = refl

positiveWitnessKeepsComplaintReviewRegression :
  Cross.CompassionWithoutSelfErasure.complaintReviewPreserved
    Cross.canonicalCompassionWithoutSelfErasure ≡ true
positiveWitnessKeepsComplaintReviewRegression = refl

positiveWitnessRejectsSelfErasureRegression :
  Cross.CompassionWithoutSelfErasure.selfErasureRequired
    Cross.canonicalCompassionWithoutSelfErasure ≡ false
positiveWitnessRejectsSelfErasureRegression =
  Cross.compassionWithoutSelfErasureDoesNotRequireSelfErasure
