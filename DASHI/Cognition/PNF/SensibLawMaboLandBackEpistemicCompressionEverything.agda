module DASHI.Cognition.PNF.SensibLawMaboLandBackEpistemicCompressionEverything where

------------------------------------------------------------------------
-- Preferred epistemic-compression capstone.
--
-- Extends the attributed/paraconsistent LAND BACK surface with the generic
-- dominant-chart compiler and the feminist/intersectional/anti-psychologising/
-- Amalek cross-pollination. It also carries the terra-nullius functional legal
-- effect classification and the Billy effective-remedy / Two-Eyed Seeing braid.
-- It does not merge those traditions into one doctrine and does not treat
-- property/asset vocabulary as the ontology of Country.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.DominantChartEpistemicCompressionExact as Compression
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Cognition.PNF.SensibLawMaboLandBackParaconsistentAttributedEverything as Previous
import DASHI.Cognition.PNF.SensibLawDominantChartEpistemicCompressionCrossPollinationExact as Cross
import DASHI.Cognition.PNF.SensibLawMaboCrownRecognitionProjectionNonFactorabilityExact as Crown
import DASHI.Cognition.PNF.SensibLawLandBackIncomeProjectionNonFactorabilityExact as Income
import DASHI.Cognition.PNF.SensibLawIndigenousCarbonValueProjectionNonFactorabilityExact as Carbon
import DASHI.Cognition.PNF.SensibLawMaboTerraNulliusJuridicalDehumanisationExact as Terra
import DASHI.Cognition.PNF.SensibLawBillyEffectiveRemedyTwoEyedSeeingExact as Billy
import DASHI.Culture.AmalekAuthorityProjectionBoundary as Amalek

------------------------------------------------------------------------
-- Prior attributed/paraconsistent state stays live.
------------------------------------------------------------------------

previousCapstoneStillCarriesCrossOrderConflict :
  Previous.crownExhaustiveSourceClaimRemainsConflicting
  ≡ Previous.crownExhaustiveSourceClaimRemainsConflicting
previousCapstoneStillCarriesCrossOrderConflict = refl

previousDawsonClosureStillNarrow :
  Previous.narrowClosureDoesNotImplyGlobalResolution
  ≡ Previous.narrowClosureDoesNotImplyGlobalResolution
previousDawsonClosureStillNarrow = refl

------------------------------------------------------------------------
-- The three SensibLaw institutional observers are instances, not analogies only.
------------------------------------------------------------------------

crownProjectionInstance :
  Compression.ProjectionInadequacyReceipt
    Crown.crownRecognitionObserver Crown.indigenousAuthorityOutcome
crownProjectionInstance = Cross.crownRecognitionCompression

incomeProjectionInstance :
  Compression.ProjectionInadequacyReceipt
    Income.cashIncomeObserver Income.landAuthorityOutcome
incomeProjectionInstance = Cross.cashIncomeCompression

biaProjectionInstance :
  Compression.ProjectionInadequacyReceipt
    Carbon.trustAssetObserver Carbon.stewardshipValueOutcome
biaProjectionInstance = Cross.biaTrustAssetAdministrativeCompression

crownProjectionCannotFactor :
  INF.FactorsThrough Crown.crownRecognitionObserver Crown.indigenousAuthorityOutcome → ⊥
crownProjectionCannotFactor = Cross.crownRecognitionCannotCarryCountryCommunityAuthority

incomeProjectionCannotFactor :
  INF.FactorsThrough Income.cashIncomeObserver Income.landAuthorityOutcome → ⊥
incomeProjectionCannotFactor = Cross.cashIncomeCannotCarryCollectiveLandAuthority

biaProjectionCannotFactor :
  INF.FactorsThrough Carbon.trustAssetObserver Carbon.stewardshipValueOutcome → ⊥
biaProjectionCannotFactor = Cross.biaCategoryCannotCarryStewardshipRelation

------------------------------------------------------------------------
-- Explicit answer to the generic audit question.
------------------------------------------------------------------------

record EpistemicCompressionQuestion : Set where
  constructor epistemic-compression-question
  field
    question : String
    answerForm : String
    requiresCollisionWitness : Bool
    requiresCollisionWitnessIsTrue : requiresCollisionWitness ≡ true
    requiresConsumerTarget : Bool
    requiresConsumerTargetIsTrue : requiresConsumerTarget ≡ true
    permitsObserverOntologyPromotion : Bool
    permitsObserverOntologyPromotionIsFalse : permitsObserverOntologyPromotion ≡ false

open EpistemicCompressionQuestion public

canonicalEpistemicCompressionQuestion : EpistemicCompressionQuestion
canonicalEpistemicCompressionQuestion = epistemic-compression-question
  "What distinctions does this institution, category, metric or representation make impossible to see for the consumer at hand?"
  "Exhibit two situated states that collide under the observer but differ under the consumer-relevant target; retain the resulting residual and specify what added observer would distinguish them."
  true refl
  true refl
  false refl

------------------------------------------------------------------------
-- Anti-capitalist / communist vocabulary audit is explicit.
------------------------------------------------------------------------

countryRelationVocabulary : Cross.CountryRelationVocabularyBoundary
countryRelationVocabulary = Cross.canonicalCountryRelationVocabularyBoundary

countryRelationIsNotAssetByDefault :
  Cross.countryRelationIsAssetByDefault countryRelationVocabulary ≡ false
countryRelationIsNotAssetByDefault = refl

propertyTitleDoesNotExhaustIndigenousAuthority :
  Cross.indigenousAuthorityReducedToPropertyTitle countryRelationVocabulary ≡ false
propertyTitleDoesNotExhaustIndigenousAuthority = refl

biaTrustAssetIsOnlySourceAdministrativeVocabulary :
  Cross.biaTrustAssetPhraseRetainedOnlyAsSourceAdministrativeCategory
    countryRelationVocabulary ≡ true
biaTrustAssetIsOnlySourceAdministrativeVocabulary = refl

commodityFormIsNotUniversalNeutralOntology :
  Cross.commodityFormIsNeutralUniversalOntology countryRelationVocabulary ≡ false
commodityFormIsNotUniversalNeutralOntology = refl

antiCapitalistLens : Cross.AuditLensBoundary
antiCapitalistLens = Cross.antiCapitalistAuditBoundary

communistMaterialRelationLens : Cross.AuditLensBoundary
communistMaterialRelationLens = Cross.communistMaterialRelationBoundary

antiCapitalistLensDoesNotProveIntent :
  Cross.automaticallyProvesNamedInstitutionIntent antiCapitalistLens ≡ false
antiCapitalistLensDoesNotProveIntent = refl

communistLensDoesNotCreateWorldTruth :
  Cross.automaticallyBecomesWorldTruth communistMaterialRelationLens ≡ false
communistLensDoesNotCreateWorldTruth = refl

------------------------------------------------------------------------
-- Feminist/intersectional result: progressive relabelling is not enough.
------------------------------------------------------------------------

posthocRewordingCannotRepairCrownProjection :
  ∀ {Recharted : Set} →
  (rechart : Crown.CrownRecognitionObservation → Recharted) →
  INF.FactorsThrough
    (λ state → rechart (Crown.crownRecognitionObserver state))
    Crown.indigenousAuthorityOutcome → ⊥
posthocRewordingCannotRepairCrownProjection = Cross.crownRewordingCannotRecoverErasedAuthority

posthocReweightingCannotRepairIncomeProjection :
  ∀ {Recharted : Set} →
  (rechart : Income.CashIncomeObservation → Recharted) →
  INF.FactorsThrough
    (λ state → rechart (Income.cashIncomeObserver state))
    Income.landAuthorityOutcome → ⊥
posthocReweightingCannotRepairIncomeProjection = Cross.incomeReweightingCannotRecoverErasedRelation

posthocBiaRelabellingCannotRepairStewardshipProjection :
  ∀ {Recharted : Set} →
  (rechart : Carbon.TrustAssetProjection → Recharted) →
  INF.FactorsThrough
    (λ state → rechart (Carbon.trustAssetObserver state))
    Carbon.stewardshipValueOutcome → ⊥
posthocBiaRelabellingCannotRepairStewardshipProjection =
  Cross.biaReclassificationCannotRecoverStewardshipRelation

------------------------------------------------------------------------
-- Terra nullius: operative legal effect can be classified without inventing a
-- quotation or a biological proposition.
------------------------------------------------------------------------

terraNulliusFunctionalJuridicalDehumanisation :
  Terra.FunctionalJuridicalDehumanisation
terraNulliusFunctionalJuridicalDehumanisation =
  Terra.terraNulliusFunctionalJuridicalDehumanisation

terraNulliusTreatedInhabitedCountryAsLegallyUninhabited :
  Terra.treatedAsLegallyUninhabited terraNulliusFunctionalJuridicalDehumanisation ≡ true
terraNulliusTreatedInhabitedCountryAsLegallyUninhabited = refl

terraNulliusDeniedIndigenousSovereigntyConstitutiveStanding :
  Terra.indigenousSovereigntyDeniedConstitutiveStanding
    terraNulliusFunctionalJuridicalDehumanisation ≡ true
terraNulliusDeniedIndigenousSovereigntyConstitutiveStanding = refl

terraNulliusDeniedOccupancyProprietaryStanding :
  Terra.occupancyDeniedProprietaryStanding
    terraNulliusFunctionalJuridicalDehumanisation ≡ true
terraNulliusDeniedOccupancyProprietaryStanding = refl

biologicalNonHumanHoldingIsNotRequiredForFunctionalClassification :
  Terra.biologicalNonHumanPropositionRequired
    terraNulliusFunctionalJuridicalDehumanisation ≡ false
biologicalNonHumanHoldingIsNotRequiredForFunctionalClassification = refl

brennanNotGivenOurFunctionalPhrase :
  Terra.BrennanUsedOurFunctionalDehumanisationPhrase → ⊥
brennanNotGivenOurFunctionalPhrase = Terra.ourPhraseDoesNotTransferToBrennan

systemEffectClassificationIsNotSpeakerQuotation :
  Terra.effectClassificationEqualsSpeakerQuotation Terra.terraNulliusSystemReading ≡ false
systemEffectClassificationIsNotSpeakerQuotation = refl

systemEffectClassificationDoesNotRequirePrivateMotive :
  Terra.effectClassificationProvesPrivateMotive Terra.terraNulliusSystemReading ≡ false
systemEffectClassificationDoesNotRequirePrivateMotive = refl

------------------------------------------------------------------------
-- Billy: full reparation is conjunctive and remains publicly incomplete.
------------------------------------------------------------------------

billyFullReparationStatus : Billy.FullReparationStatus
billyFullReparationStatus = Billy.currentPublicFullReparationStatus

billyPublicFullReparationResidualLive :
  billyFullReparationStatus ≡ Billy.fullReparationResidualLive
billyPublicFullReparationResidualLive = refl

billyCompensationReceiptNotRecovered :
  Billy.publicImplementationState Billy.adequateCompensation
  ≡ Billy.publicReceiptNotRecovered
billyCompensationReceiptNotRecovered = refl

billyConsultationEvidencePresent :
  Billy.publicImplementationState Billy.meaningfulConsultation
  ≡ Billy.publicEvidencePresent
billyConsultationEvidencePresent = refl

billySafeExistenceMeasuresEvidencePresent :
  Billy.publicImplementationState Billy.continuedSafeExistenceMeasures
  ≡ Billy.publicEvidencePresent
billySafeExistenceMeasuresEvidencePresent = refl

billyDirectCommitteeExecutionWritUnavailableByDefault :
  Billy.mechanismStrength Billy.directTreatyBodyDomesticExecutionWrit
  ≡ Billy.unavailableByDefault
billyDirectCommitteeExecutionWritUnavailableByDefault = refl

billyTreatyFollowUpIsIndirectLeverage :
  Billy.mechanismStrength Billy.treatyBodyFollowUpProcedure
  ≡ Billy.availableIndirect
billyTreatyFollowUpIsIndirectLeverage = refl

billyCompensationProspectPoliticallyContingent :
  Billy.prospectFor Billy.adequateCompensation ≡ Billy.politicallyContingentProspect
billyCompensationProspectPoliticallyContingent = refl

billyConsultationDoesNotCloseFullReparation :
  Billy.ConsultationEqualsFullReparation → ⊥
billyConsultationDoesNotCloseFullReparation = Billy.consultationDoesNotEqualFullReparation

billyAdaptationFundingDoesNotBecomeCompensation :
  Billy.AdaptationFundingEqualsCompensation → ⊥
billyAdaptationFundingDoesNotBecomeCompensation = Billy.adaptationFundingDoesNotEqualCompensation

------------------------------------------------------------------------
-- Two-Eyed Seeing / Sweetgrass: coordination without extraction or fusion.
------------------------------------------------------------------------

billyRemedyConsultationBoundary : Billy.RemedyConsultationBoundary
billyRemedyConsultationBoundary = Billy.canonicalRemedyConsultationBoundary

billyCommunityObservationDoesNotTransferAuthorityToState :
  Billy.hearingCommunityObservationEqualsTransferringAuthority
    billyRemedyConsultationBoundary ≡ false
billyCommunityObservationDoesNotTransferAuthorityToState = refl

billyConsultationMayEraseProvenanceAndObligation :
  Billy.consultationMayEraseProvenanceAndObligation
    billyRemedyConsultationBoundary ≡ true
billyConsultationMayEraseProvenanceAndObligation = refl

billyCommunityDefinedNeedsRequired :
  Billy.adequateConsultationRequiresCommunityDefinedNeeds
    billyRemedyConsultationBoundary ≡ true
billyCommunityDefinedNeedsRequired = refl

billyMonitoringRequiresCommunityFeedbackLoop :
  Billy.monitoringRequiresCommunityFeedbackLoop
    billyRemedyConsultationBoundary ≡ true
billyMonitoringRequiresCommunityFeedbackLoop = refl

billyRemedyCanCoordinateWithoutEpistemicFusion :
  Billy.remedyCanBeCoordinatedWithoutEpistemicFusion
    billyRemedyConsultationBoundary ≡ true
billyRemedyCanCoordinateWithoutEpistemicFusion = refl

------------------------------------------------------------------------
-- "A system is what it does": declared commitment != realised remedy.
------------------------------------------------------------------------

billyOperationalSemantics : Billy.RemedyOperationalSemantics
billyOperationalSemantics = Billy.canonicalRemedyOperationalSemantics

billyDeclarationAloneDoesNotCloseRemedy :
  Billy.declarationAloneClosesRemedy billyOperationalSemantics ≡ false
billyDeclarationAloneDoesNotCloseRemedy = refl

billyFundingAnnouncementDoesNotCloseCompensation :
  Billy.fundingAnnouncementAloneClosesCompensationCoordinate
    billyOperationalSemantics ≡ false
billyFundingAnnouncementDoesNotCloseCompensation = refl

billyConsultationMeetingDoesNotCloseNeedsAssessment :
  Billy.consultationMeetingAloneClosesNeedsAssessment billyOperationalSemantics ≡ false
billyConsultationMeetingDoesNotCloseNeedsAssessment = refl

billyRealisedSafetyAndCulturalContinuityMatter :
  Billy.realisedCommunitySafetyAndCulturalContinuityMatter
    billyOperationalSemantics ≡ true
billyRealisedSafetyAndCulturalContinuityMatter = refl

billyImplementationMustUseCommunityDefinedOutcomeFeedback :
  Billy.implementationMustBeMonitoredAgainstCommunityDefinedOutcome
    billyOperationalSemantics ≡ true
billyImplementationMustUseCommunityDefinedOutcomeFeedback = refl

------------------------------------------------------------------------
-- Amalek is the correction-closure frontier, not a synonym for coarse-graining.
------------------------------------------------------------------------

amalekClosedLoop : Amalek.ClosedAuthorityLoop
amalekClosedLoop = Amalek.canonicalClosedAuthorityRisk

closedAuthorityLoopHasNoIndependentCorrection :
  Amalek.correctionChannelIndependent amalekClosedLoop ≡ false
closedAuthorityLoopHasNoIndependentCorrection = refl

terminalisationIsNotOnlyOrdinaryProjection :
  Compression.terminalisationIsOnlyOrdinaryProjectionLoss
    Compression.canonicalTerminalisationRiskBoundary ≡ false
terminalisationIsNotOnlyOrdinaryProjection = refl

terminalisationCanReclassifyDissentAsConfirmingFault :
  Compression.terminalisationMayReclassifyDissentAsConfirmingFault
    Compression.canonicalTerminalisationRiskBoundary ≡ true
terminalisationCanReclassifyDissentAsConfirmingFault = refl

humanGroupEnemyPromotionRemainsForbidden :
  Compression.humanGroupMayBePromotedToTerminalEnemyPredicate
    Compression.canonicalTerminalisationRiskBoundary ≡ false
humanGroupEnemyPromotionRemainsForbidden = refl

------------------------------------------------------------------------
-- Deep epistemic boundary.
------------------------------------------------------------------------

record DeepEpistemicBoundary : Set where
  constructor deep-epistemic-boundary
  field
    localTechnicalAdequacyMeansOntologicalExhaustiveness : Bool
    localTechnicalAdequacyMeansOntologicalExhaustivenessIsFalse :
      localTechnicalAdequacyMeansOntologicalExhaustiveness ≡ false
    institutionalVisibilityConstitutesExistence : Bool
    institutionalVisibilityConstitutesExistenceIsFalse :
      institutionalVisibilityConstitutesExistence ≡ false
    dominantObserverDefinesOnlyLegitimateReality : Bool
    dominantObserverDefinesOnlyLegitimateRealityIsFalse :
      dominantObserverDefinesOnlyLegitimateReality ≡ false
    omittedResidualMayBePoliticallyMaterial : Bool
    omittedResidualMayBePoliticallyMaterialIsTrue :
      omittedResidualMayBePoliticallyMaterial ≡ true
    observerCritiqueMakesObserverUselessForEveryConsumer : Bool
    observerCritiqueMakesObserverUselessForEveryConsumerIsFalse :
      observerCritiqueMakesObserverUselessForEveryConsumer ≡ false
    correctionRequiresAddedInformationWhenCollisionExists : Bool
    correctionRequiresAddedInformationWhenCollisionExistsIsTrue :
      correctionRequiresAddedInformationWhenCollisionExists ≡ true
    conflictMayRemainWithoutLogicalExplosion : Bool
    conflictMayRemainWithoutLogicalExplosionIsTrue :
      conflictMayRemainWithoutLogicalExplosion ≡ true

open DeepEpistemicBoundary public

canonicalDeepEpistemicBoundary : DeepEpistemicBoundary
canonicalDeepEpistemicBoundary = deep-epistemic-boundary
  false refl
  false refl
  false refl
  true refl
  false refl
  true refl
  true refl

------------------------------------------------------------------------
-- No universal synthesis.
------------------------------------------------------------------------

data DeepEpistemicPointProvesOneMasterTheory : Set where
data FormalNonfactorabilityAutomaticallyProvesOppression : Set where
data CommunistAuditMakesCommunityAuthorityExternalTheory : Set where

deepPointDoesNotProveOneMasterTheory : DeepEpistemicPointProvesOneMasterTheory → ⊥
deepPointDoesNotProveOneMasterTheory ()

nonfactorabilityDoesNotAutomaticallyProveOppression :
  FormalNonfactorabilityAutomaticallyProvesOppression → ⊥
nonfactorabilityDoesNotAutomaticallyProveOppression ()

communistAuditDoesNotAppropriateCommunityAuthority :
  CommunistAuditMakesCommunityAuthorityExternalTheory → ⊥
communistAuditDoesNotAppropriateCommunityAuthority ()
