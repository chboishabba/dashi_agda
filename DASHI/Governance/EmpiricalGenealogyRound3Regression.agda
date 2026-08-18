module DASHI.Governance.EmpiricalGenealogyRound3Regression where

open import DASHI.Core.Prelude

import DASHI.Governance.EvidenceGradedGenealogyCore as Genealogy
import DASHI.Governance.EvidenceGradedGenealogyCasesExact as Cases
import DASHI.Governance.TypedGenealogyEdgeExact as Typed
import DASHI.Governance.ClimateGenealogyTypedCasesExact as Climate
import DASHI.Governance.JohnPaperClaimPromotionAuditExact as Paper
import DASHI.Governance.JohnPaperClaimManifestV2Exact as Manifest
import DASHI.Governance.PalantirProcurementLegibilityAdapterExact as Palantir
import DASHI.Governance.MinimalSufficientObservationGovernanceExact as Minimal
import DASHI.Governance.MultidimensionalContestabilityAccessExact as Access
import DASHI.Governance.DependentReligiousEntrapmentCandidateExact as Entrapment
import DASHI.Governance.EvolvingCapacityReligiousAutonomyExact as Capacity
import DASHI.Governance.CoercionConfinementLegalSeparationExact as Legal
import DASHI.Governance.ColonialCarceralDependencyAuthorityBridgeExact as Colonial
import DASHI.Governance.EffectiveInstitutionalChoiceExact as Choice
import DASHI.Governance.DelegatedEssentialServiceAuthorityExact as Service
import DASHI.Governance.InstitutionalDependencyEntrapmentBridgeExact as InstitutionalEntrapment
import DASHI.Governance.AliceBrownInstitutionalAgencyChoiceBridgeExact as Alice
import DASHI.Governance.IndigenousRemovalDelegatedInfrastructureExact as Removal
import DASHI.Governance.EffectiveChoiceConcentrationExact as Concentration
import DASHI.Governance.AustralianSupermarketChoiceConcentrationExact as Supermarket
import DASHI.Governance.AustralianTwoPartyPreferredObservationExact as TPP
import DASHI.Governance.SituatedEffectiveChoiceExact as Situated
import DASHI.Governance.PluralityWithoutPowerParityExact as Parity
import DASHI.Governance.AuthorityBearingLegibilityFailureExact as Legibility
import DASHI.Governance.BurkeWillsSituatedKnowledgeCounterexampleExact as BurkeWills
import DASHI.Governance.QuotedUtteranceContextProvenanceExact as Quote
import DASHI.Governance.BraidedEnemyRoleProvenanceCrossPollinationExact as Braid

------------------------------------------------------------------------
-- Focused local-kernel regression root.
--
-- Suggested local command:
--   agda -i . DASHI/Governance/EmpiricalGenealogyRound3Regression.agda
------------------------------------------------------------------------

tobaccoFoodHasGradeAStrongEdge :
  Genealogy.StrongEvidenceEdge Cases.tobaccoToFoodTransfer
tobaccoFoodHasGradeAStrongEdge = Cases.tobaccoToFoodIsStrong

tobaccoClimateHasGradeBStrongEdge :
  Genealogy.StrongEvidenceEdge Cases.tobaccoToClimateHistoricalContinuity
tobaccoClimateHasGradeBStrongEdge = Cases.tobaccoToClimateIsStrong

wellnessAntiVaxAdjacencyDoesNotBecomeStrongTransfer :
  Genealogy.StrongEvidenceEdge Cases.wellnessToAntiVaxAdjacency → ⊥
wellnessAntiVaxAdjacencyDoesNotBecomeStrongTransfer =
  Cases.wellnessAdjacencyIsNotStrongHistoricalTransfer

tradwifeAltRightCandidateStillNeedsEvidence :
  Cases.CandidateConnectionPromotesToStrongGenealogy → ⊥
tradwifeAltRightCandidateStillNeedsEvidence =
  Cases.candidateConnectionDoesNotPromoteWithoutReceipt

primaryMethodRecurrenceStillNotHistoricalTransfer :
  Typed.StrongHistoricalTransfer Climate.bwToAPIRecurrence → ⊥
primaryMethodRecurrenceStillNotHistoricalTransfer =
  Climate.recurrenceCannotBePromotedByPrimaryQualityAlone

pendingTransferStillNeedsBridge :
  Typed.StrongHistoricalTransfer Climate.bwToAPIHistoricalTransferPending → ⊥
pendingTransferStillNeedsBridge = Climate.pendingHistoricalTransferIsNotStrongYet

singerRemainsUnresolvedNotStrong :
  Typed.StrongEvidence
    (Typed.evidenceStrength Climate.singerTobaccoContinuityCandidate) → ⊥
singerRemainsUnresolvedNotStrong = Climate.singerCandidateIsNotStrong

relationAndEvidenceAreIndependentAxes :
  Typed.TypedGenealogyBoundary.relationAndEvidenceAreSeparateAxes
    Typed.canonicalTypedGenealogyBoundary
  ≡ true
relationAndEvidenceAreIndependentAxes = refl

paperFraudReceiptNotInstalled :
  Paper.JohnPaperPromotionAudit.fraudExternalLegalReceiptInstalled
    Paper.canonicalJohnPaperPromotionAudit
  ≡ false
paperFraudReceiptNotInstalled = refl

paperBatteryReceiptNotInstalled :
  Paper.JohnPaperPromotionAudit.batteryExternalLegalReceiptInstalled
    Paper.canonicalJohnPaperPromotionAudit
  ≡ false
paperBatteryReceiptNotInstalled = refl

paperModernSlaveryReceiptNotInstalled :
  Paper.JohnPaperPromotionAudit.modernSlaveryExternalLegalReceiptInstalled
    Paper.canonicalJohnPaperPromotionAudit
  ≡ false
paperModernSlaveryReceiptNotInstalled = refl

paperLegalPromotionRequiresJurisdictionReceipt :
  Paper.JohnPaperPromotionAudit.legalPromotionRequiresJurisdictionSpecificReceipt
    Paper.canonicalJohnPaperPromotionAudit
  ≡ true
paperLegalPromotionRequiresJurisdictionReceipt = refl

manifestConstructAndApplicationSeparated :
  Manifest.ManifestV2Boundary.constructAndApplicationSeparated
    Manifest.canonicalManifestV2Boundary
  ≡ true
manifestConstructAndApplicationSeparated = refl

manifestMechanismDoesNotCreateEtiology :
  Manifest.ManifestV2Boundary.mechanismAndEtiologySeparated
    Manifest.canonicalManifestV2Boundary
  ≡ true
manifestMechanismDoesNotCreateEtiology = refl

palantirProcurementEvidenceExists :
  Palantir.PalantirProcurementAdapterBoundary.procurementEvidenceInstalled
    Palantir.canonicalPalantirProcurementAdapterBoundary
  ≡ true
palantirProcurementEvidenceExists = refl

palantirAsymmetryStillUnconstructed :
  Palantir.PalantirProcurementAdapterBoundary.subjectInstitutionAsymmetryWitnessInstalled
    Palantir.canonicalPalantirProcurementAdapterBoundary
  ≡ false
palantirAsymmetryStillUnconstructed = refl

canonicalFutureQuotientHasMinimalityDirection :
  Minimal.MinimalObservationBoundary.canonicalFutureCodeFactorsThroughEverySectionedSafeProjection
    Minimal.canonicalMinimalObservationBoundary
  ≡ true
canonicalFutureQuotientHasMinimalityDirection = refl

scalarContestabilityBudgetCanHideBottleneck :
  Access.ResourceAccessWithin Access.bottleneckDemand Access.spreadBudget → ⊥
scalarContestabilityBudgetCanHideBottleneck =
  Access.aggregateSufficiencyDoesNotEstablishCoordinateAccess

ordinaryTeachingDoesNotEqualEntrapment :
  Entrapment.DependentReligiousEntrapmentBoundary.ordinaryReligiousTeachingEqualsEntrapment
    Entrapment.canonicalDependentReligiousEntrapmentBoundary
  ≡ false
ordinaryTeachingDoesNotEqualEntrapment = refl

entrapmentMechanismsCanIncludeBelongingAndDivineSanction :
  Entrapment.DependentReligiousEntrapmentBoundary.familyBelongingPenaltyCanBeRelevantMechanism
    Entrapment.canonicalDependentReligiousEntrapmentBoundary
  ≡ true
entrapmentMechanismsCanIncludeBelongingAndDivineSanction = refl

age18IsNotReligiousConsentSwitch :
  Capacity.EvolvingCapacityReligiousAutonomyBoundary.fixedAge18ReligiousConsentSwitch
    Capacity.canonicalEvolvingCapacityReligiousAutonomyBoundary
  ≡ false
age18IsNotReligiousConsentSwitch = refl

formationBeforeEpistemicIndependenceIsRelevant :
  Capacity.EvolvingCapacityReligiousAutonomyBoundary.formationBeforeEpistemicIndependenceRelevant
    Capacity.canonicalEvolvingCapacityReligiousAutonomyBoundary
  ≡ true
formationBeforeEpistemicIndependenceIsRelevant = refl

psychologicalCoercionDoesNotEqualSlavery :
  Legal.CoercionConfinementLegalBoundary.socialEntrapmentEqualsSlavery
    Legal.canonicalCoercionConfinementLegalBoundary
  ≡ false
psychologicalCoercionDoesNotEqualSlavery = refl

servitudeStillNeedsLabourOrServicesReceipt :
  Legal.CoercionConfinementLegalBoundary.servitudeRequiresAdditionalLabourOrServicesReceipt
    Legal.canonicalCoercionConfinementLegalBoundary
  ≡ true
servitudeStillNeedsLabourOrServicesReceipt = refl

colonialCarceralComparisonDoesNotCollapseDomains :
  Colonial.ColonialCarceralDependencyBoundary.colonialSystemEqualsCarceralSystem
    Colonial.canonicalColonialCarceralDependencyBoundary
  ≡ false
colonialCarceralComparisonDoesNotCollapseDomains = refl

sharedDependencyAuthorityExitTopologyIsAvailable :
  Colonial.ColonialCarceralDependencyBoundary.dependencyAuthorityExitTopologyShared
    Colonial.canonicalColonialCarceralDependencyBoundary
  ≡ true
sharedDependencyAuthorityExitTopologyIsAvailable = refl

formalInstitutionalPluralityIsNotEffectivePlurality :
  Choice.EffectiveInstitutionalChoiceBoundary.formalPluralityEqualsEffectivePlurality
    Choice.canonicalEffectiveInstitutionalChoiceBoundary
  ≡ false
formalInstitutionalPluralityIsNotEffectivePlurality = refl

coordinateBottleneckCanDestroyAlternative :
  Choice.EffectivelyAccessible Choice.secularSchoolDemand Choice.canonicalFamilyCapacity → ⊥
coordinateBottleneckCanDestroyAlternative = Choice.secularSchoolNotAccessible

religiousAvailabilityAloneDoesNotEstablishCoercion :
  Choice.EffectiveInstitutionalChoiceBoundary.onlyAccessibleReligiousProviderEqualsCoercion
    Choice.canonicalEffectiveInstitutionalChoiceBoundary
  ≡ false
religiousAvailabilityAloneDoesNotEstablishCoercion = refl

healthcareStrictEqualityIsReused :
  Service.DelegatedEssentialServiceBoundary.healthcareStrictEqualityReused
    Service.canonicalDelegatedEssentialServiceBoundary
  ≡ true
healthcareStrictEqualityIsReused = refl

dependencyNeedsAdditionalCoerciveUseWitness :
  InstitutionalEntrapment.InstitutionalDependencyEntrapmentBoundary.coerciveUseRequiresAdditionalWitness
    InstitutionalEntrapment.canonicalInstitutionalDependencyEntrapmentBoundary
  ≡ true
dependencyNeedsAdditionalCoerciveUseWitness = refl

aliceFormalAvailabilityDoesNotEqualAgency :
  Alice.AliceInstitutionalChoiceBoundary.formalAvailabilityEqualsAgency
    Alice.canonicalAliceInstitutionalChoiceBoundary
  ≡ false
aliceFormalAvailabilityDoesNotEqualAgency = refl

aliceParentExpertiseCanRemainSituatedEvidence :
  Alice.AliceInstitutionalChoiceBoundary.parentExpertiseMayBeSituatedEvidence
    Alice.canonicalAliceInstitutionalChoiceBoundary
  ≡ true
aliceParentExpertiseCanRemainSituatedEvidence = refl

dominantPairDoesNotEqualMonopoly :
  Concentration.EffectiveChoiceConcentrationBoundary.dominantPairEqualsMonopoly
    Concentration.canonicalEffectiveChoiceConcentrationBoundary
  ≡ false
dominantPairDoesNotEqualMonopoly = refl

effectiveMonopolyStillDoesNotEqualCoercion :
  Concentration.EffectiveChoiceConcentrationBoundary.monopolyEqualsCoercion
    Concentration.canonicalEffectiveChoiceConcentrationBoundary
  ≡ false
effectiveMonopolyStillDoesNotEqualCoercion = refl

coerciveUseStillRequiresSeparateWitness :
  Concentration.EffectiveChoiceConcentrationBoundary.coerciveUseRequiresSeparateWitness
    Concentration.canonicalEffectiveChoiceConcentrationBoundary
  ≡ true
coerciveUseStillRequiresSeparateWitness = refl

acccConcentrationDoesNotBecomeLiteralDuopoly :
  Supermarket.AustralianSupermarketChoiceBoundary.dominantPairShareEqualsLiteralDuopoly
    Supermarket.canonicalAustralianSupermarketChoiceBoundary
  ≡ false
acccConcentrationDoesNotBecomeLiteralDuopoly = refl

supermarketObserverSubstitutionCanRemainDistinct :
  Supermarket.AustralianSupermarketChoiceBoundary.observerRelativeSubstitutabilityRetained
    Supermarket.canonicalAustralianSupermarketChoiceBoundary
  ≡ true
supermarketObserverSubstitutionCanRemainDistinct = refl

tppCompressionLosesSomeFirstPreferenceResolution :
  TPP.AustralianTPPObservationBoundary.tppPreservesEveryFirstPreferenceDistinction
    TPP.canonicalAustralianTPPObservationBoundary
  ≡ false
tppCompressionLosesSomeFirstPreferenceResolution = refl

tppDoesNotPromoteLiteralPoliticalDuopoly :
  TPP.AustralianTPPObservationBoundary.tppEqualsLiteralPoliticalDuopoly
    TPP.canonicalAustralianTPPObservationBoundary
  ≡ false
tppDoesNotPromoteLiteralPoliticalDuopoly = refl

tppFiniteWitnessIsNonInjective : TPP.TPPInjective → ⊥
tppFiniteWitnessIsNonInjective = TPP.tppObservationIsNotInjective

------------------------------------------------------------------------
-- Situated choice / plurality-power / colonial legibility / situated knowledge.
------------------------------------------------------------------------

nationalPluralityDoesNotGuaranteeLocalChoice :
  Situated.SituatedEffectiveChoiceBoundary.nationalPluralityEqualsLocalEffectivePlurality
    Situated.canonicalSituatedEffectiveChoiceBoundary
  ≡ false
nationalPluralityDoesNotGuaranteeLocalChoice = refl

remoteGeometryCanChangeReachability :
  Situated.Reachable Situated.farProvider Situated.remoteResources → ⊥
remoteGeometryCanChangeReachability = Situated.remoteCannotReachFarProvider

nominalPluralityDoesNotGuaranteePowerParity :
  Parity.PluralityWithoutPowerParityBoundary.nominalPluralityEqualsInstitutionalParity
    Parity.canonicalPluralityWithoutPowerParityBoundary
  ≡ false
nominalPluralityDoesNotGuaranteePowerParity = refl

legalVictoryDoesNotGuaranteeInstitutionalDislodgement :
  Parity.PluralityWithoutPowerParityBoundary.legalCorrectionEqualsMaterialDislodgement
    Parity.canonicalPluralityWithoutPowerParityBoundary
  ≡ false
legalVictoryDoesNotGuaranteeInstitutionalDislodgement = refl

lossyRepresentationCanFeedAuthority :
  Legibility.AuthorityBearingLegibilityBoundary.lossyRepresentationCanFeedInstitutionalAction
    Legibility.canonicalAuthorityBearingLegibilityBoundary
  ≡ true
lossyRepresentationCanFeedAuthority = refl

maboCorrectionDoesNotByItselfEstablishMaterialRepair :
  Legibility.AuthorityBearingLegibilityBoundary.judicialCorrectionEqualsCompleteMaterialRepair
    Legibility.canonicalAuthorityBearingLegibilityBoundary
  ≡ false
maboCorrectionDoesNotByItselfEstablishMaterialRepair = refl

burkeWillsReceivedIndigenousAssistance :
  BurkeWills.BurkeWillsSituatedKnowledgeBoundary.expeditionReceivedIndigenousAssistance
    BurkeWills.canonicalBurkeWillsSituatedKnowledgeBoundary
  ≡ true
burkeWillsReceivedIndigenousAssistance = refl

burkeWillsDoesNotBecomeNeverUsedKnowledgeNarrative :
  BurkeWills.BurkeWillsSituatedKnowledgeBoundary.assistanceWasConsistentlyInstitutionalised
    BurkeWills.canonicalBurkeWillsSituatedKnowledgeBoundary
  ≡ false
burkeWillsDoesNotBecomeNeverUsedKnowledgeNarrative = refl

removalInfrastructureSeparatesStateAndNonStateRoles :
  Removal.IndigenousDelegatedInfrastructureBoundary.stateAndNonStateRolesSeparated
    Removal.canonicalIndigenousDelegatedInfrastructureBoundary
  ≡ true
removalInfrastructureSeparatesStateAndNonStateRoles = refl

removalInfrastructureDoesNotClaimWholeLegalAuthority :
  Removal.IndigenousDelegatedInfrastructureBoundary.operationalParticipationEqualsWholeLegalAuthority
    Removal.canonicalIndigenousDelegatedInfrastructureBoundary
  ≡ false
removalInfrastructureDoesNotClaimWholeLegalAuthority = refl

quoteContextDoesNotEraseLiteralUtterance :
  Quote.QuotedUtteranceBoundary.clarificationErasesQuote
    Quote.canonicalQuotedUtteranceBoundary
  ≡ false
quoteContextDoesNotEraseLiteralUtterance = refl

quoteDoesNotAloneEstablishMotive :
  Quote.QuotedUtteranceBoundary.quoteAloneEstablishesMotive
    Quote.canonicalQuotedUtteranceBoundary
  ≡ false
quoteDoesNotAloneEstablishMotive = refl

absoluteEnemyCompressionCanLoseResolution :
  Braid.BraidedEnemyRoleBoundary.absoluteEnemyCompressionCanLoseActorResolution
    Braid.canonicalBraidedEnemyRoleBoundary
  ≡ true
absoluteEnemyCompressionCanLoseResolution = refl

braidedProvenanceDoesNotClaimIndigenousKnowledge :
  Braid.BraidedEnemyRoleBoundary.indigenousKnowledgeClaimedByFormalAnalogy
    Braid.canonicalBraidedEnemyRoleBoundary
  ≡ false
braidedProvenanceDoesNotClaimIndigenousKnowledge = refl
