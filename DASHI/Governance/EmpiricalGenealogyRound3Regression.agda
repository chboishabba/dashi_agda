module DASHI.Governance.EmpiricalGenealogyRound3Regression where

open import DASHI.Core.Prelude

import DASHI.Governance.EvidenceGradedGenealogyCore as Genealogy
import DASHI.Governance.EvidenceGradedGenealogyCasesExact as Cases
import DASHI.Governance.TypedGenealogyEdgeExact as Typed
import DASHI.Governance.ClimateGenealogyTypedCasesExact as Climate
import DASHI.Core.InstitutionalProximityInfluenceAdequacyExact as Proximity
import DASHI.Core.IntersectionalNonFactorability as INF
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


------------------------------------------------------------------------
-- 2026-10-26: climate-source-producer bridge and selective non-promotion.
-- Named team contributors / historic funders / later speakers have typed
-- receipts, but are not thereby joined into an unbroken control hierarchy.
------------------------------------------------------------------------

exxonAPIPlanParticipantIsExplicitlyNamed :
  Typed.evidenceStrength Climate.apiNamedContributorRandyRandol ≡ Typed.primary
exxonAPIPlanParticipantIsExplicitlyNamed = refl

cfactAPIPlanParticipantIsExplicitlyNamed :
  Typed.evidenceStrength Climate.apiNamedContributorDavidRothbard ≡ Typed.primary
cfactAPIPlanParticipantIsExplicitlyNamed = refl

historicHancockIPAMoneyIsFundingNotAnEditorialOrder :
  Typed.relationKind Climate.hancockIPAHistoricalDonations ≡ Typed.funding
historicHancockIPAMoneyIsFundingNotAnEditorialOrder = refl

shellDepartureIsRecordedHistoricalOrganisationChange :
  Typed.relationKind Climate.shellGCCDefection1998 ≡ Typed.organisationalContinuity
shellDepartureIsRecordedHistoricalOrganisationChange = refl

mooreCO2ChairIsAffiliationNotProofOfCommission :
  Typed.relationKind Climate.mooreCO2Chair ≡ Typed.personnelContinuity
mooreCO2ChairIsAffiliationNotProofOfCommission = refl

apiPlanParticipationCannotBecomeMethodTransmission :
  Typed.StrongHistoricalTransfer Climate.apiNamedContributorRandyRandol → ⊥
apiPlanParticipationCannotBecomeMethodTransmission =
  Climate.apiContributorNotMethodTransfer

hancockIPAFundingCannotBecomeAutomaticMessageControl :
  Typed.StrongHistoricalTransfer Climate.hancockIPAHistoricalDonations → ⊥
hancockIPAFundingCannotBecomeAutomaticMessageControl =
  Climate.ipaFundingNotEditorialMethod

cfact1998And2026DoNotAutomaticallyProveContinuousPlan :
  Typed.StrongHistoricalTransfer Climate.cfactAPITo2026Continuity → ⊥
cfact1998And2026DoNotAutomaticallyProveContinuousPlan =
  Climate.cfactContinuationNotPlanTransfer

foundationIncomeNotSameAsClimateDenialExpenditure :
  Climate.ConcentratedSourceAuditBoundary.total900mOrganisationRevenueIsClimateSpecificSpending
    Climate.canonicalConcentratedSourceAuditBoundary ≡ false
foundationIncomeNotSameAsClimateDenialExpenditure = refl

industryDefectionsNotErased :
  Climate.ConcentratedSourceAuditBoundary.shellBPDefectionsPreservedAsCounterExamples
    Climate.canonicalConcentratedSourceAuditBoundary ≡ true
industryDefectionsNotErased = refl


allAPIContributorsInExampleShareOneOriginalDocument :
  Typed.receipts Climate.apiNamedContributorAJohnAdams ≡
  Typed.receipts Climate.apiNamedContributorJosephWalker
allAPIContributorsInExampleShareOneOriginalDocument = refl


milloy1998To2021IsPersonnelNotScriptTransmission :
  Typed.relationKind Climate.milloy1998ToReefMedia ≡ Typed.personnelContinuity
milloy1998To2021IsPersonnelNotScriptTransmission = refl

repeatPersonDoesNotProveOriginalAPIPlanStillActive :
  Typed.StrongHistoricalTransfer Climate.milloy1998ToReefMedia → ⊥
repeatPersonDoesNotProveOriginalAPIPlanStillActive =
  Climate.milloyRepeatNotProofOfTwentyThreeYearPlan


singerGCCBudgetIsRequestNotPaidGrant :
  Typed.relationKind Climate.singerGCCSolicitationNotMoneyPaid ≡ Typed.fundingProposal
singerGCCBudgetIsRequestNotPaidGrant = refl

southernICEBudgetIsCommitmentNotBankTransfer :
  Typed.relationKind Climate.southernICEPledgeNotDisbursement ≡ Typed.fundingCommitment
southernICEBudgetIsCommitmentNotBankTransfer = refl

singer1994ProposalCannotEstablishMethodTransfer :
  Typed.StrongHistoricalTransfer Climate.singerGCCSolicitationNotMoneyPaid → ⊥
singer1994ProposalCannotEstablishMethodTransfer =
  Climate.fundingRequestIsNotTransfer

southern1991PledgeCannotEstablishMethodTransfer :
  Typed.StrongHistoricalTransfer Climate.southernICEPledgeNotDisbursement → ⊥
southern1991PledgeCannotEstablishMethodTransfer =
  Climate.fundingPledgeIsNotTransfer


gccACSHResearchWasCommissionedAccordingToArchive :
  Typed.relationKind Climate.gccACSHCommissionedClimateHealth ≡ Typed.commissionedResearch
gccACSHResearchWasCommissionedAccordingToArchive = refl

gccACSHClientReviewRightsNotProofOfActualEditing :
  Typed.relationKind Climate.gccACSHDocumentedEditorialReviewRights ≡ Typed.editorialReviewRights
gccACSHClientReviewRightsNotProofOfActualEditing = refl

gccACSHPublishedSubjectOverlapNotSameFile :
  Typed.relationKind Climate.gccACSH1997PublicPaperMatch ≡ Typed.topicalPublicationMatch
gccACSHPublishedSubjectOverlapNotSameFile = refl

exxonLaterCHCFundingIsBoundedHistoricalReporting :
  Typed.evidenceStrength Climate.exxonToCHCReportedPostAPIGrants ≡ Typed.corroborated
exxonLaterCHCFundingIsBoundedHistoricalReporting = refl

acshTopicalMatchCannotProveTransfer :
  Typed.StrongHistoricalTransfer Climate.gccACSH1997PublicPaperMatch → ⊥
acshTopicalMatchCannotProveTransfer =
  Climate.gccACSHSharedSubjectNotIdenticalFinalFile

acshEditorialDiscretionDoesNotProveSpecificScientificEdit :
  Typed.StrongHistoricalTransfer Climate.gccACSHDocumentedEditorialReviewRights → ⊥
acshEditorialDiscretionDoesNotProveSpecificScientificEdit =
  Climate.gccACSHContractualRightsNotProofOfSpecificScientificEdit

singerGCCProposalUnacquiredDocumentIsCorroborated :
  Typed.evidenceStrength Climate.singerGCCSolicitationNotMoneyPaid ≡ Typed.corroborated
singerGCCProposalUnacquiredDocumentIsCorroborated = refl


------------------------------------------------------------------------
-- Historical climate commissioning consumer: exact source identity,
-- separately typed exposure, and ALREADY-PROVED proximity inadequacy.
-- Reuse, not a second independent-influence no-go construction.
------------------------------------------------------------------------

acshPublicArgumentHasFirstPartySource :
  Typed.identifier Climate.acsh1997OriginalPublicArgument ≡
    "https://www.acsh.org/news/1997/10/01/global-climate-change-and-human-health"
acshPublicArgumentHasFirstPartySource = refl

gcc2001KyotoScriptIsExposureNotVerdict :
  Typed.relationKind Climate.gcc2001DraftPolicyInputAcknowledgment ≡
    Typed.recommendationExposure
gcc2001KyotoScriptIsExposureNotVerdict = refl

gccStateDepartmentReportedAccessDoesNotProveMethodTransfer :
  Typed.StrongHistoricalTransfer Climate.gcc2001DraftPolicyInputAcknowledgment → ⊥
gccStateDepartmentReportedAccessDoesNotProveMethodTransfer =
  Climate.policyAccessIsNotCompletedMethodTransfer

donorActorInstitutionProximityDoesNotEstablishDecisionControl :
  Proximity.InfluenceThroughProximity → ⊥
donorActorInstitutionProximityDoesNotEstablishDecisionControl =
  Proximity.influenceDoesNotFactorThroughProximity


------------------------------------------------------------------------
-- Repeated exact 2026 Australian financial headline is not the number of
-- underlying independent estimation paths; a 25 percent tax rate does not
-- disclose whether PRRT is replaced or retained. Ibrahim dependence
-- barrier reused, not reimplemented.
------------------------------------------------------------------------

australiaInstitute17BSourceRestatedInSenate :
  Typed.relationKind Climate.tai17BRestatedByPocock2026 ≡
    Typed.reportedStatisticRestatement
australiaInstitute17BSourceRestatedInSenate = refl

arthurDLittle17BSourceRestatedInSenate :
  Typed.relationKind Climate.futureGroup17BRestatedByPocock2026 ≡
    Typed.reportedStatisticRestatement
arthurDLittle17BSourceRestatedInSenate = refl

hancockCreditedOriginalJournalismReuse :
  Typed.relationKind Climate.nightlyToHancockExplicitReprint2026 ≡
    Typed.explicitAttributedRepublication
hancockCreditedOriginalJournalismReuse = refl

aepWoodMacResultNotAScientificReplicate :
  Typed.relationKind Climate.aepWoodMacStatisticsNotNationalTaxRate ≡
    Typed.reportedStatisticRestatement
aepWoodMacResultNotAScientificReplicate = refl

actuReplacementDistinctFromAdditionalLevy :
  Typed.relationKind Climate.actuReplacementVsAEPAddOnSpecification ≡
    Typed.parallelEconomicArgument
actuReplacementDistinctFromAdditionalLevy = refl

same17BHeadlineDoesNotIdentifyNamedModelCount :
  INF.FactorsThrough Climate.same17BPrinted Climate.namedModelSourceCount → ⊥
same17BHeadlineDoesNotIdentifyNamedModelCount =
  Climate.annual17BHeadlineCannotRevealModelAncestry

same25PcHeadlineDoesNotIdentifyTaxDesign :
  INF.FactorsThrough Climate.taxRateLabel Climate.taxPolicyMeaning → ⊥
same25PcHeadlineDoesNotIdentifyTaxDesign =
  Climate.same25PcCannotDetermineInstrument

creditedReprintIsNotDirectHistoricalMethodTransfer :
  Typed.StrongHistoricalTransfer Climate.nightlyToHancockExplicitReprint2026 → ⊥
creditedReprintIsNotDirectHistoricalMethodTransfer =
  Climate.hancockReprintIsNotIndependentMethodTransmission

actuWoodMacPolicyComparisonDoesNotProveSharedScript :
  Typed.StrongHistoricalTransfer Climate.actuReplacementVsAEPAddOnSpecification → ⊥
actuWoodMacPolicyComparisonDoesNotProveSharedScript =
  Climate.taxSchemeSimilarityNotScriptCopy


aep2025ForecastTo2026PaidHeadlineHasSameInstitution :
  Typed.relationKind Climate.aepForecastToPaidStatusRestatement ≡
    Typed.reportedStatisticRestatement
aep2025ForecastTo2026PaidHeadlineHasSameInstitution = refl

same21Point9BNumberDoesNotEstablishActualityStatus :
  INF.FactorsThrough Climate.same21BPrinted Climate.reportedStatusFor21B → ⊥
same21Point9BNumberDoesNotEstablishActualityStatus =
  Climate.sameTaxNumberCannotDetermineSourceStatus


------------------------------------------------------------------------
-- 27 October source-acquired Arthur D. Little report, one model and
-- multiple policy bases. Two existing Ibrahim factorisation obstructions
-- are consumed here without introducing duplicate evidence machinery.
------------------------------------------------------------------------

adlFirstPartyConsultantReportCommissioned :
  Typed.relationKind Climate.adlReportCommissionedAndPublic ≡ Typed.commissionedResearch
adlFirstPartyConsultantReportCommissioned = refl

adlFirstYearUpperBoundNotTenYearGuarantee :
  Typed.relationKind Climate.adlSeventeenBFirstYearUpperBoundNotTenYearCash ≡
    Typed.reportedStatisticRestatement
adlFirstYearUpperBoundNotTenYearGuarantee = refl

adlReturnsUnitSummaryNotAnotherEconomicModel :
  Typed.relationKind Climate.adlIRRPointsVersusFutureGroupReturnsPercent ≡
    Typed.reportedStatisticRestatement
adlReturnsUnitSummaryNotAnotherEconomicModel = refl

same25NominalRateCannotDetermineADLTenYearRevenue :
  INF.FactorsThrough Climate.adlHeadlineRate Climate.adlTenYearBand → ⊥
same25NominalRateCannotDetermineADLTenYearRevenue =
  Climate.adlSame25RateCannotDetermineDecadeRevenue

bareTwoPercentCannotDetermineIRRChangeUnits :
  INF.FactorsThrough Climate.returnHeadlineWithoutUnits Climate.returnChangeUnit → ⊥
bareTwoPercentCannotDetermineIRRChangeUnits =
  Climate.bareTwoPercentCannotIdentifyReturnUnit

futureGroupRestatementNotDirectMethodTransfer :
  Typed.StrongHistoricalTransfer Climate.adlIRRPointsVersusFutureGroupReturnsPercent → ⊥
futureGroupRestatementNotDirectMethodTransfer =
  Climate.adlFirstPartyScenarioIsNotProofOfEditorialTransfer


------------------------------------------------------------------------
-- Original Wood Mackenzie 16-page study; no promotion of commissioned
-- hypothesis to national tax paid or equivalence with replacement PRRT.
------------------------------------------------------------------------

woodMackenzieOriginalConfirmsAEPClientRestatement :
  Typed.relationKind Climate.woodMackenzieOriginalIsAEPCommission ≡
    Typed.reportedStatisticRestatement
woodMackenzieOriginalConfirmsAEPClientRestatement = refl

woodMackenzieAndACTUAreNotSameTaxDesign :
  Typed.relationKind Climate.woodMackenzieAppendixNotACTUReplacement ≡
    Typed.parallelEconomicArgument
woodMackenzieAndACTUAreNotSameTaxDesign = refl

woodMackenzieContractedVsADLSpotSourceModel :
  Typed.relationKind Climate.woodMackenzieNoSpotVersusADLMarginalSpot ≡
    Typed.parallelEconomicArgument
woodMackenzieContractedVsADLSpotSourceModel = refl

woodMackenzieSameRateCannotConcealSpotAssumption :
  INF.FactorsThrough Climate.sameNominalRateAcrossModels Climate.originalModelContractingAssumption → ⊥
woodMackenzieSameRateCannotConcealSpotAssumption =
  Climate.same25RateCannotDetermineModelSpotAssumption


------------------------------------------------------------------------
-- Named government originals, reservation percentage denominators, and
-- future-tense commencement claims are source-versioned rather than enacted.
------------------------------------------------------------------------

governmentReservation2025VersusMay2026Base :
  Typed.relationKind Climate.reservation2025ProductionToMay2026Exports ≡
    Typed.reportedStatisticRestatement
governmentReservation2025VersusMay2026Base = refl

governmentReservationDutyDateIsDraftSourceSequence :
  Typed.relationKind Climate.reservationMayToSeptemberDutyDate ≡
    Typed.reportedStatisticRestatement
governmentReservationDutyDateIsDraftSourceSequence = refl

governmentReservationDateDriftDoesNotProveTransfer :
  Typed.StrongHistoricalTransfer Climate.reservationMayToSeptemberDutyDate → ⊥
governmentReservationDateDriftDoesNotProveTransfer =
  Climate.reservationDraftChronologyIsNotMethodTransmission


------------------------------------------------------------------------
-- Introduced gas reservation package: primary original release versus
-- recorded attributed first-person Hansard; proposed administrative levy
-- must never absorb ADL's 25%-of-export-sales fiscal counterfactual.
------------------------------------------------------------------------

octoberBillIsIntroducedNotCertifiedEnacted :
  Typed.relationKind Climate.octoberGasBillsIntroduced2026 ≡
    Typed.legislativeIntroduction
octoberBillIsIntroducedNotCertifiedEnacted = refl

octoberBillIntroductionNotHistoricalDirection :
  Typed.StrongHistoricalTransfer Climate.octoberGasBillsIntroduced2026 → ⊥
octoberBillIntroductionNotHistoricalDirection =
  Climate.octoberBillIntroCannotEstablishHistoricalTransfer

octoberCostRecoveryNotAdValoremTax :
  Typed.relationKind Climate.octoberCostRecoveryLevyNotRevenueTax ≡
    Typed.parallelEconomicArgument
octoberCostRecoveryNotAdValoremTax = refl

octoberAdditionalityDesignOnly :
  Typed.relationKind Climate.octoberAdditionalityNotObservedDeliveredSupply ≡
    Typed.legislativeIntroduction
octoberAdditionalityDesignOnly = refl

octoberBareLevyStringNotInstrumentIdentifier :
  INF.FactorsThrough Climate.displayedLevyWord Climate.legalBaseOfLevy → ⊥
octoberBareLevyStringNotInstrumentIdentifier =
  Climate.bareLevyLabelCannotRecoverTaxBase
