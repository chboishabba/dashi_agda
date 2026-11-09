module DASHI.Cognition.CCDCOEP3CausalTrialecticRegressionExact where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Empty using (⊥)

import Base369 as Base
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.BinaryInteractionNonseparabilityExact as Interaction
import DASHI.Cognition.CCDCOEP3TypedIntersectionalAxisExact as Axis
import DASHI.Cognition.CCDCOEP3SituatedHistoryPNFExact as History
import DASHI.Core.DiscriminatorSynthesisExact as Discriminator
import DASHI.Cognition.PNF.EventAlgebra as PNF
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Perm
import DASHI.Foundations.TernaryPermutationS3LawsExact as S3
import DASHI.Cognition.CCDCOEP3CausalTrialecticInteractionExact as P3
import DASHI.Cognition.CCDCOEP3ClimateGenealogyCaseExact as ClimateCase
import DASHI.Cognition.CCDCOEP3API1998PrimaryPlanExact as API1998
import DASHI.Cognition.CCDCOEP3EvidenceStageIdentificationExact as Ladder
import DASHI.Cognition.CCDCOEP3PreAPIOpinionTemporalControlExact as PreAPI
import DASHI.Cognition.CCDCOEP3ClimateContestedAttributionExact as Contested
import DASHI.Cognition.CCDCOEP3ClimateObservedActivityAndCorpusExact as Observed
import DASHI.Cognition.CCDCOEP3GCCExecutedCampaignSourceExact as GCC
import DASHI.Cognition.CCDCOEP3Trumbo1996IndependentMediaBaselineExact as Trumbo
import DASHI.Cognition.CCDCOEP3G20COP21AttributionExact as Institution
import DASHI.Cognition.CCDCOEP3G20ComplianceObservedExact as Compliance
import DASHI.Cognition.CCDCOEP3CountryImplementationJoinExact as Country
import DASHI.Cognition.CCDCOEP3G20RGMemberPanelExact as MemberPanel
import DASHI.Cognition.CCDCOEP3StakeholderHandoffExact as Handoff
import DASHI.Cognition.CCDCOEP3CulturalSourceGenreExact as Culture
import DASHI.Cognition.CCDCOEP3CognitiveWarfareArtDiscriminatorExact as CW
import DASHI.Cognition.CCDCOEP3GCC1993SourceChainExact as GCC1993
import DASHI.Cognition.CCDCOEP3GCC1993DirectionDiscriminatorExact as Direction
import DASHI.Cognition.CCDCOEP3GCC1993ClaimCodingAdmissionExact as Coding
import DASHI.Cognition.CCDCOEP3GCC1993PreResponseBaselineExact as Baseline
import DASHI.Cognition.CCDCOEP3GCC1993PreResponseExpandedExact as Expanded
import DASHI.Cognition.CCDCOEP3SourcePowerEvidenceWeldExact as Source
import DASHI.Culture.JohnAnthonyBrownChildReligiousPowerBidiExact as Brown
import DASHI.Governance.EvidenceGradedGenealogyCore as Genealogy
import DASHI.Wikimedia.IbrahimSnowballAnthropologyClimateDenialPoliticalTheologyExact as Climate

-- The two axes have different indexed point carriers despite their
-- equal finite point counts. Their contextual response is not recovered
-- by adding, counting, or recharting those point coordinates.

typedRaceSexNotIdentical :
  Axis.raceAxis ≡ Axis.sexAxis → ⊥
typedRaceSexNotIdentical = P3.typedRaceSexAxesDistinct

typedIntersectionIsNotEndpointAdditive :
  Interaction.NonseparableAdditiveInteraction Axis.typedJointSurface
typedIntersectionIsNotEndpointAdditive =
  P3.typedInteractionHasNoEndpointAdditiveReconstruction

sameTypedPositionsDoNotFixSituatedOutcome :
  NF.FactorsThrough Axis.coordinatesOnly Axis.recognition → ⊥
sameTypedPositionsDoNotFixSituatedOutcome =
  P3.sameTypedCoordinatesDoNotDetermineSituatedRecognition

-- A positive context observation separates the originally indistinguishable
-- pair. It cannot be simulated by recharting the two axis coordinates.
contextualDiscriminatorClosesTheSelectedPair :
  Discriminator.BundleSeparates Axis.contextualObservationBundle
    Axis.sameCoordinatesAccessible Axis.sameCoordinatesExclusionary
contextualDiscriminatorClosesTheSelectedPair =
  Axis.contextualObservationSeparates

historicalCandidateCannotBeAutoPromoted :
  ∀ {About}
    (evidence : History.SituatedEventEvidence About) →
  PNF.candidateOnly (History.originalCandidate evidence) ≡ true
historicalCandidateCannotBeAutoPromoted =
  History.candidateStatusPreserved

originalS3Reverse :
  Perm.applyPermutation
    (Perm.inversePermutation Perm.permRotate)
    (Perm.applyPermutation Perm.permRotate Base.tri-low)
  ≡ Base.tri-low
originalS3Reverse =
  P3.sixReorientationsReversible Perm.permRotate Base.tri-low

originalS3OrderObstruction :
  S3._∙_ Perm.permRotate Perm.permSwapLowMid
  ≡ S3._∙_ Perm.permSwapLowMid Perm.permRotate → ⊥
originalS3OrderObstruction = P3.orderOfS3OperationsMatters

causalWorldsLookIdentical :
  P3.observedPairFor P3.directEffect
  ≡ P3.observedPairFor P3.commonCause
causalWorldsLookIdentical = P3.observedDistributionsIdentical

selectedProbeDoesSeparate :
  Discriminator.BundleSeparates
    P3.counterfactualDistinguishingProbe
    P3.directEffect P3.commonCause
selectedProbeDoesSeparate = P3.counterfactualProbeSeparates

noCausalInferenceFromObservationsAlone :
  NF.FactorsThrough P3.observedPairFor P3.interventionalProbe → ⊥
noCausalInferenceFromObservationsAlone =
  P3.observationalAssociationDoesNotIdentifyCausation

noIntentFromMeasuredEffectAlone :
  NF.FactorsThrough P3.observedEffect P3.worldPurpose → ⊥
noIntentFromMeasuredEffectAlone =
  P3.effectCannotIdentifyHostilePurpose

coherenceDoesNotFixEpistemicRevision :
  NF.FactorsThrough P3.publicCoherence P3.evidenceRevision → ⊥
coherenceDoesNotFixEpistemicRevision =
  P3.narrativeCoherenceDoesNotDetermineRevisability

revisionMeasurementSeparatesCoherenceCollision :
  Discriminator.BundleSeparates
    P3.revisabilityDistinguishingProbe
    P3.coherentAndContestable P3.coherentButSelfSealed
revisionMeasurementSeparatesCoherenceCollision =
  P3.revisionProbeSeparates

denialSurfaceCannotIdentifyMeaning :
  NF.FactorsThrough Climate.projectDenialSurface
    Climate.denialSocialReading → ⊥
denialSurfaceCannotIdentifyMeaning =
  Source.climateDenialLabelCannotIdentifySocialCause

brownInstitutionalPowerIsOriginalAxis :
  Brown.BrownPaperClaim.axis Brown.institutionalHegemonyClaim
  ≡ Brown.institutionalPower
brownInstitutionalPowerIsOriginalAxis =
  Source.brownPaperContainsInstitutionalHegemonyAxis

-- The actual tobacco-to-climate historical continuity is grade B,
-- rather than a certificate of central command or a belief-change effect.
climateCaseHistoricallyStrong :
  Genealogy.StrongEvidenceEdge ClimateCase.originalClimateContinuity
climateCaseHistoricallyStrong =
  ClimateCase.historicalContinuityHasStrongReceipt

climateCaseCannotInferCentralCommand :
  NF.FactorsThrough ClimateCase.publicHistoricalGrade
    ClimateCase.commandHypothesis → ⊥
climateCaseCannotInferCentralCommand =
  ClimateCase.gradeBDoesNotIdentifyCentralCommand

climateCaseHypotheticalCommandDiscriminator :
  Discriminator.BundleSeparates
    ClimateCase.candidateCommandProbe
    ClimateCase.decentralisedCandidate ClimateCase.centralisedCandidate
climateCaseHypotheticalCommandDiscriminator =
  ClimateCase.centralisationHypothesesCanBeSeparatedIfEvidenceExists

-- A contemporaneous Congressional Record primary plan is evidence of
-- drafting and intended tactics, NOT documentary proof of their execution.
primaryDraftDoesNotEstablishImplementation :
  NF.FactorsThrough API1998.publicDraftObservation API1998.implementation → ⊥
primaryDraftDoesNotEstablishImplementation =
  API1998.draftDocumentDoesNotIdentifyImplementation

primaryDraftAndActualImplementationWouldSeparate :
  Discriminator.BundleSeparates API1998.implementationEvidenceProbe
    API1998.unimplementedWorld API1998.implementedWorld
primaryDraftAndActualImplementationWouldSeparate =
  API1998.implementationEvidenceSeparates

-- Source-type and organisation-authority are NOT interchangeable claims.
-- The 1998 API response and the historical Congressional draft remain
-- distinct source objects; the existence of the draft does not settle
-- the attributed dispute over corporate adoption.
climateSourceTypeMustRemainDistinguishable :
  NF.FactorsThrough Contested.flattenSource Contested.sourceDisposition → ⊥
climateSourceTypeMustRemainDistinguishable =
  Contested.sourceKindNotIdentifiedByTopic

apiInstitutionalAuthorisationStillUnderidentified :
  NF.FactorsThrough Contested.publishedDraft
    Contested.authorityHypothesis → ⊥
apiInstitutionalAuthorisationStillUnderidentified =
  Contested.publishedDraftCannotProveInstitutionalAuthorisation

originalApprovalRecordsWouldSeparateAlternatives :
  Discriminator.BundleSeparates Contested.authorisationRecordProbe
    Contested.unapprovedWorld Contested.approvedWorld
originalApprovalRecordsWouldSeparateAlternatives =
  Contested.authorisationRecordWouldSeparate

-- Independent public communication materials exist while the April 1998
-- API document retains the type of a draft. The original publication
-- does not support a causal or same-plan command/effect promotion.
realPublicationIsNotThe1998Draft :
  NF.FactorsThrough Observed.unqualifiedLabel Observed.sourceStage → ⊥
realPublicationIsNotThe1998Draft =
  Observed.stageDoesNotFactorThroughGenericLabel

realArchiveStageDiscriminator :
  Discriminator.BundleSeparates Observed.evidenceStageBundle
    Observed.apiDraft1998 Observed.ice1991
realArchiveStageDiscriminator =
  Observed.stageSeparatesDraftFromPublicCommunication

publishedCommunicationCorpusHas187Documents :
  Observed.PublishedCorpusMeasurement.totalDocuments
    Observed.originalPublishedCorpusMeasurement ≡ 187
publishedCommunicationCorpusHas187Documents =
  Observed.publishedCorpusSize

publishedMessageDiscrepancyDoesNotMeasurePersuasion :
  Observed.PublishedCorpusMeasurement.isHumanTreatmentEffect
    Observed.originalPublishedCorpusMeasurement ≡ false
publishedMessageDiscrepancyDoesNotMeasurePersuasion =
  Observed.documentContentIsNotPublicBeliefEffect

preplanPollIsNotPostCampaignEffect :
  API1998.ReportedPreplanSurvey.wasPostImplementationFollowup
    API1998.charltonSurveyAsDescribedInDraft ≡ false
preplanPollIsNotPostCampaignEffect =
  API1998.surveyIsNotMeasuredPostImplementationImpact

proposedBudgetDoesNotEqualPaidReceipt :
  API1998.PlannedAmounts.actualPaidReceiptsAdmitted
    API1998.amountsProposedInDraft ≡ false
proposedBudgetDoesNotEqualPaidReceipt =
  API1998.noPaymentEstablishedByDraft

-- Successively different evidence/consumer requirements:
-- draft != approval != funding != delivery != established effect.
-- Each named non-factorability proof reuses the canonical owner.
draftDoesNotIdentifyAPIApproval :
  NF.FactorsThrough Ladder.draftKnown Ladder.approvalKnown → ⊥
draftDoesNotIdentifyAPIApproval = Ladder.draftDoesNotDetermineApproval

approvalDoesNotIdentifyDisbursement :
  NF.FactorsThrough Ladder.approvalKnown Ladder.fundingKnown → ⊥
approvalDoesNotIdentifyDisbursement = Ladder.approvalDoesNotDetermineFunding

fundingDoesNotIdentifyCampaignDelivery :
  NF.FactorsThrough Ladder.fundingKnown Ladder.deliveryKnown → ⊥
fundingDoesNotIdentifyCampaignDelivery = Ladder.fundingDoesNotDetermineDelivery

deliveryDoesNotIdentifyPersuasion :
  NF.FactorsThrough Ladder.deliveryKnown Ladder.effectEstablished → ⊥
deliveryDoesNotIdentifyPersuasion = Ladder.deliveryDoesNotDetermineEffect

fundingRecordsWouldDiscriminate :
  Discriminator.BundleSeparates Ladder.fundingSourceProbe
    Ladder.approvedWithoutFunding Ladder.fundedWithoutDelivery
fundingRecordsWouldDiscriminate = Ladder.fundingProbeSeparates

-- Real historical survey measurements precede the selected 1998 plan.
-- The exact 1997 survey response change is not an effect of the later
-- plan, regardless of its interpretation as general climate concern.
previousSurveysDoNotIdentifyLaterCampaignEffect :
  NF.FactorsThrough PreAPI.observedEarlierWaves PreAPI.laterImpact → ⊥
previousSurveysDoNotIdentifyLaterCampaignEffect =
  PreAPI.earlierSurveyCannotIdentifyLaterCampaignEffect

prePlanNewsAwarenessChange :
  PreAPI.reportedPercentage PreAPI.recalledNewsCoverage
    PreAPI.before1997KyotoDebate + 8
  ≡ PreAPI.reportedPercentage PreAPI.recalledNewsCoverage
    PreAPI.after1997DebateBeforeAPIDraft
prePlanNewsAwarenessChange = PreAPI.newsExposureDifference

-- The 26 April 1998 attributed journalistic account is a temporal
-- status report, not certified final non-funding or final non-approval.
contemporaneousFundingStillHasNoFinalReceipt :
  Contested.Original1998FundingStatusReport.actualFinalFundingReceiptPresent
    Contested.contemporaneousNoApprovalReport ≡ false
contemporaneousFundingStillHasNoFinalReceipt =
  Contested.actualFundingNotEstablished

contemporaneousApprovalStillHasNoFinalReceipt :
  Contested.Original1998FundingStatusReport.actualFinalApprovalReceiptPresent
    Contested.contemporaneousNoApprovalReport ≡ false
contemporaneousApprovalStillHasNoFinalReceipt =
  Contested.actualApprovalNotEstablished

laterOrganiserAttributionIsNotAuditedExpenditure :
  Contested.RetrospectiveAttribution.negativeAccountingIndependentReceipt
    Contested.walkerAttributedRetrospective ≡ false
laterOrganiserAttributionIsNotAuditedExpenditure =
  Contested.retrospectiveIsNotFundProof

-- Source scope: direct published 2021 interview is first-person
-- testimony, not a signed company financial closeout.
namedExecutive2021SaysNonfunding :
  Contested.FormerExecutive2021Account.saysSpecificPlanNeverFunded
    Contested.okeefe2021AttributedAccount ≡ true
namedExecutive2021SaysNonfunding =
  Contested.publishedNamedParticipantSaysNoFunding

namedExecutive2021SaysWorkshopOccurred :
  Contested.FormerExecutive2021Account.saysMultiOrganisationWorkshopOccurred
    Contested.okeefe2021AttributedAccount ≡ true
namedExecutive2021SaysWorkshopOccurred =
  Contested.publishedNamedParticipantSaysPlanningOccurred

namedExecutive2021DoesNotSupplyAccounting :
  Contested.FormerExecutive2021Account.independentCompanyAccountingAdmitted
    Contested.okeefe2021AttributedAccount ≡ false
namedExecutive2021DoesNotSupplyAccounting =
  Contested.directInterviewIsNotIndependentAccounting

-- GCC Harrison agency case history and archived 1993 media objects
-- MUST retain their original source-kind identity. The firms' own
-- claimed policy/media effects are not observed causal estimates.
gccAgencyReportIsNotIndependentMediaArchive :
  NF.FactorsThrough GCC.flatten GCC.kind → ⊥
gccAgencyReportIsNotIndependentMediaArchive =
  GCC.evidenceKindDoesNotFactorThroughGenericTopic

gccSourceKindProbeSeparates :
  Discriminator.BundleSeparates GCC.sourceIdentityProbe
    GCC.harrisonFirmCaseHistory GCC.gccHeldMediaClippings1993
gccSourceKindProbeSeparates = GCC.sourceIdentitySeparates

gccRealSourceDoesNotInventEffect :
  GCC.GCCMediaReplicationGate.causalEffectAdmitted
    GCC.selectedGCCCaseGate ≡ false
gccRealSourceDoesNotInventEffect = GCC.noInventedCausalEstimate

-- Actual independent 1996 five-newspaper media observations have real
-- published volume summaries and coder agreement, but do NOT supply
-- GCC programme-specific effects or establish the PR firm's claim.
trumboPublishedCoverageNotGCCEffect :
  NF.FactorsThrough Trumbo.sameReportedBaseline
    Trumbo.differentUnobservedExplanations → ⊥
trumboPublishedCoverageNotGCCEffect =
  Trumbo.independentVolumeDoesNotIdentifyAgencyCausality

trumboFrameReliabilityReported :
  Trumbo.IndependentMediaContentStudy.sourceScopedFrameReliabilityNumerator
    Trumbo.trumbo1996PublishedStudy ≡ 78
trumboFrameReliabilityReported =
  Trumbo.reportedScottPiTimes100

trumboOriginalCausalEffectNotAdmitted :
  Trumbo.IndependentMediaContentStudy.independentGCCEffectMeasured
    Trumbo.trumbo1996PublishedStudy ≡ false
trumboOriginalCausalEffectNotAdmitted =
  Trumbo.independentBaselineDoesNotReportGCCEffect

-- Independent G20/COP21 original document authorship preserved:
-- Hamburg's United States statement must not be attributed to
-- the other G20 leaders, nor B20/C20 recommendations to G20 adoption.
hamburgUSOtherG20SpeakersNotFlattenable :
  NF.FactorsThrough Institution.flattenTopic Institution.speaker → ⊥
hamburgUSOtherG20SpeakersNotFlattenable =
  Institution.hamburgAttributionCannotFactorThroughTopic

c20RecommendationNotParisLegalDuty :
  NF.FactorsThrough Institution.flattenTopic Institution.speechAct → ⊥
c20RecommendationNotParisLegalDuty =
  Institution.legalSpeechActCannotFactorThroughTopic

gCCAgencyAccountNotParisLegalAuthority :
  NF.FactorsThrough Institution.flattenTopic Institution.strength → ⊥
gCCAgencyAccountNotParisLegalAuthority =
  Institution.agencySelfAssessmentNotTreatyAuthority

hamburgSeparateVoicesProbe :
  Discriminator.BundleSeparates Institution.institutionalVoiceProbe
    Institution.hamburgUS2017 Institution.hamburgOtherLeaders2017
hamburgSeparateVoicesProbe =
  Institution.hamburgSpeakerSeparation

noEndorsementFromSummitCitation :
  Institution.InstitutionallyScopedSource.externalAuthorsEndorseDASHI
    Institution.hamburgSource ≡ false
noEndorsementFromSummitCitation =
  Institution.noEndorsementFromQuotation

-- Original empirical ownership: G20 Research Group, NOT leaders' own
-- self-evaluation. Different selected topic and year denominators.
brisbaneClimateG20RGObserved :
  Compliance.reportedPercent Compliance.brisbaneClimate ≡ 55
brisbaneClimateG20RGObserved =
  Compliance.brisbaneClimateReported

brisbaneFossilG20RGObserved :
  Compliance.reportedPercent Compliance.brisbaneFossil ≡ 28
brisbaneFossilG20RGObserved =
  Compliance.brisbaneFossilReported

antalyaFossilG20RGObserved :
  Compliance.reportedPercent Compliance.antalyaFossil ≡ 33
antalyaFossilG20RGObserved =
  Compliance.antalyaFossilReported

fossilScoreComparisonArithmeticOnly :
  Compliance.reportedPercent Compliance.brisbaneFossil + 5
  ≡ Compliance.reportedPercent Compliance.antalyaFossil
fossilScoreComparisonArithmeticOnly =
  Compliance.publishedFossilScoreDifference

noInventedIndustryAttributionForG20RG :
  Compliance.IndependentEvaluation.causalGCCOrExxonEffectMeasured
    (Compliance.study Compliance.brisbaneFinal2014) ≡ false
noInventedIndustryAttributionForG20RG =
  Compliance.noReportedClimateCausalInfluence

-- Additional real October 2015 sequence: an earlier Energy Ministers'
-- communique cannot inherit the authorship of the later B20 Energy
-- Forum Statement. Named corporate speakers and IEA/OECD/ICC inputs
-- are not independently verified individual recommendation authors.
energyMinistersAndB20SpeakersDistinct :
  NF.FactorsThrough Institution.flattenTopic Institution.speaker → ⊥
energyMinistersAndB20SpeakersDistinct =
  Institution.b20BusinessSubmissionDoesNotFactorIntoG20Author

b20ContributorsNotIdentifiedAsClauseAuthors :
  Institution.B20OriginalDocumentAttribution.originalClauseAuthorsIndividuallyVerified
    Institution.b20EnergyOriginalReceipt ≡ false
b20ContributorsNotIdentifiedAsClauseAuthors =
  Institution.b20KnownInputDoesNotEstablishIndividualAuthorship

b20SourceInputsDoNotProveAntalyaInfluence :
  Institution.B20OriginalDocumentAttribution.financeLobbyingTransmissionToLeadersVerified
    Institution.b20EnergyOriginalReceipt ≡ false
b20SourceInputsDoNotProveAntalyaInfluence =
  Institution.b20NamedInputsDoNotEstablishG20Influence

noLaterPublicationPromotedToPriorMinisterialAuthorship :
  Institution.SequenceSourceDates.laterPublishedTextProvesEarlierMinisterialAuthorship
    Institution.octoberToParisSequence ≡ false
noLaterPublicationPromotedToPriorMinisterialAuthorship =
  Institution.noBackdatedDocumentAuthorshipClaim


-- Country implementation evidence cannot be promoted from a candidate
-- stage into an independently reviewed original observation.
countryCandidateDoesNotCountAsReviewed :
  Country.candidate ≡ Country.reviewedOriginal → ⊥
countryCandidateDoesNotCountAsReviewed = Country.candidateNotReviewed

-- A reused fossil-subsidy metric is not an equality of original
-- 2014 Brisbane and 2015 Antalya assessment populations.
countryStudyOwnersDistinct :
  Country.brisbane2014 ≡ Country.antalya2015 → ⊥
countryStudyOwnersDistinct = Country.notSameStudy

-- Source-attributed G20RG member scores count to the printed narrative
-- (Brisbane -0.45, Antalya -0.35), with the Brisbane Table 2 printed
-- -0.40 discrepancy retained separately for documentary audit.
brisbaneNetMinusNine : MemberPanel.minusCount MemberPanel.brisbaneFossilMembers
  ≡ MemberPanel.plusCount MemberPanel.brisbaneFossilMembers + 9
brisbaneNetMinusNine = MemberPanel.brisbaneNineNetMinus

antalyaNetMinusSeven : MemberPanel.minusCount MemberPanel.antalyaFossilMembers
  ≡ MemberPanel.plusCount MemberPanel.antalyaFossilMembers + 7
antalyaNetMinusSeven = MemberPanel.antalyaSevenNetMinus

c20ReceiptNotG20Adoption :
  Handoff.EvidenceItem.level Handoff.c20PresidencyReceipt
  ≡ Handoff.adoptedPolicyText → ⊥
c20ReceiptNotG20Adoption = Handoff.c20ReceiptNotPolicyAdoption

b20ReportedPresentationNotDraftUptake :
  Handoff.EvidenceItem.level Handoff.b20ICCPresentationAccount
  ≡ Handoff.provedDraftUptake → ⊥
b20ReportedPresentationNotDraftUptake = Handoff.b20PresentationNotDraftUptake

-- Scholarly genealogy, policy proposal, documentary assertion and
-- fictional satire retain separate epistemic status.
filmFictionIsNotIndependentlyMeasured :
  Culture.CulturalWork.status Culture.dontLookUp2021
  ≡ Culture.independentlyVerifiedObservation → ⊥
filmFictionIsNotIndependentlyMeasured = Culture.satireNotEmpiricalObservation

greenNewDealPolicyProposalNotHistoricalEvidence :
  Culture.CulturalWork.kind Culture.chomskyPollin2020
  ≡ Culture.historicalResearch → ⊥
greenNewDealPolicyProposalNotHistoricalEvidence =
  Culture.policyProposalNotHistoricalObservation

-- The CCDCOE cognitive-warfare criterion is strictly stronger than
-- document presence, message similarity, measured content or satire.
agencyHistoryNotOriginalPressArchive :
  Discriminator.BundleSeparates GCC.sourceIdentityProbe
    GCC.harrisonFirmCaseHistory GCC.gccHeldMediaClippings1993
agencyHistoryNotOriginalPressArchive =
  CW.sourceKindDiscriminatesAgencyReportFromArchivedPress

fictionDoesNotMeasureAudience :
  Culture.CulturalWork.status Culture.dontLookUp2021
  ≡ Culture.independentlyVerifiedObservation → ⊥
fictionDoesNotMeasureAudience =
  CW.fictionalSatireNotIndependentAudienceObservation

effectDoesNotDetermineWarfareIntent :
  NF.FactorsThrough P3.observedEffect P3.worldPurpose → ⊥
effectDoesNotDetermineWarfareIntent =
  CW.measuredEffectAloneCannotIdentifyHostilePurpose

-- The 3 May reporter-directed mailing and July DOE communication
-- share the originating GCC but retain distinct original addressees.
-- Archival catalogue records do not identify actual message receipt.
gcc1993MayToJulyCannotFuseRecipients :
  GCC1993.addressedTo GCC1993.julyDepartmentOfEnergyLetter
  ≡ GCC1993.addressedTo GCC1993.mayReporterLetter → ⊥
gcc1993MayToJulyCannotFuseRecipients =
  GCC1993.doeLetterDifferentDestination

originalNewspaperBylinesRemainDistinctFromGCC :
  GCC1993.originalOwner GCC1993.archivedMediaClippings
  ≡ GCC1993.originalOwner GCC1993.mayReporterLetter → ⊥
originalNewspaperBylinesRemainDistinctFromGCC =
  GCC1993.articleAuthorNotGCCHistoricalAuthor

-- An independently authored June 1 article is the object of a later
-- GCC response, not an original article authored by GCC on June 30.
laterGCCResponseNotCauseOfPriorArticle :
  Direction.HistoricalSourceRelation
    Direction.shlaesGCCResponseJune30
    Direction.rensbergerWashingtonPostJune1 → ⊥
laterGCCResponseNotCauseOfPriorArticle =
  Direction.responseCannotBeSourceOfEarlierArticle

originalJournalistAndGCCAuthorsRemainDistinct :
  Direction.originalAuthor Direction.rensbergerWashingtonPostJune1
  ≡ Direction.originalAuthor Direction.shlaesGCCResponseJune30 → ⊥
originalJournalistAndGCCAuthorsRemainDistinct =
  Direction.journalistNotGCCHistoricalAuthor

-- Original 8 June 1993 James Hansen correction is authored by neither
-- the original Washington Post reporter nor the later GCC communicator.
independentPublishedCorrectionNotCoalitionAuthored :
  Direction.originalAuthor Direction.hansenIndependentRebuttalJune8
  ≡ Direction.originalAuthor Direction.shlaesGCCResponseJune30 → ⊥
independentPublishedCorrectionNotCoalitionAuthored =
  Direction.independentHansenLetterNotGCCAuthored

publishedHansenCorrectionNotProofOfGCCKnowledge :
  Direction.hansenRebuttalPublished
  ≡ Direction.originalActorReadAndConsidered → ⊥
publishedHansenCorrectionNotProofOfGCCKnowledge =
  Direction.publishedNotProofOfGCCKnowledge

-- A missing original GCC PDF is not evidence the communication was silent
-- about Hansen. Archive-described secondary circulation is not measured
-- readership or hostile purpose.
unreviewedGCCSourceCannotProveOmission :
  Coding.missingJuneDocument
  ≡ Coding.explicitlyAbsentInCompleteReviewedDocument → ⊥
unreviewedGCCSourceCannotProveOmission =
  Coding.missingSourceNotProvedSilence

GCCAmplificationNotAudienceExposure :
  Coding.resultConsumer Coding.archivalGCCReference
  ≡ Coding.independentReaderExposure → ⊥
GCCAmplificationNotAudienceExposure =
  Coding.archiveResultNotExposure

GCCAmplificationNotHostilePurpose :
  Coding.resultConsumer Coding.archivalGCCReference
  ≡ Coding.hostileIntention → ⊥
GCCAmplificationNotHostilePurpose =
  Coding.secondaryAmplificationNotHostilePurpose

-- GCC's catalogued 10 March 1993 public model/policy release predates
-- both the independently authored press article and its June GCC reply.
-- It cannot serve as an authenticated passage-coded numerical baseline.
originalMarchGCCReleasePrecedesJuneReply :
  Baseline.Before Baseline.marchGCCRelease Baseline.juneGCCResponse
originalMarchGCCReleasePrecedesJuneReply = Baseline.marchBeforeJune

preResponseCatalogueNotQuantitativeBaseline :
  Baseline.marchGrade ≡ Baseline.independentlyCodedOriginalText → ⊥
preResponseCatalogueNotQuantitativeBaseline = Baseline.catalogueNotCodedBaseline

-- March 8 GCC policy statement is an earlier, source-attributed
-- archive candidate than March 10 model release. The circa-1993
-- expert-quotation brochure has no certified exact date.
earlierOriginalPolicyStatement :
  Expanded.ArchivedBefore
    Expanded.marchEightPolicyStatement Expanded.marchTenModelRelease
earlierOriginalPolicyStatement =
  Expanded.marchEightBeforeMarchTen

undatedExpertBrochureCannotBeOrderedToADay :
  Expanded.datePrecision Expanded.undatedExpertSelectionBrochure
  ≡ Expanded.exactArchiveCalendarDay → ⊥
undatedExpertBrochureCannotBeOrderedToADay =
  Expanded.undatedBrochureNotAnExactDay

archiveSelectedPolicyExcerptIsNotOriginalFullText :
  Expanded.selectedPolicyGrade
  ≡ Expanded.independentlyReviewedWholeOriginal → ⊥
archiveSelectedPolicyExcerptIsNotOriginalFullText =
  Expanded.marchPolicySelectedQuoteNotCompleteOriginal
