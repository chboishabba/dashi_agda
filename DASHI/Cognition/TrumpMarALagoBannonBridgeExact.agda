module DASHI.Cognition.TrumpMarALagoBannonBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.TrumpEpsteinPoliticalRelationshipExact as TrumpEpstein
import DASHI.Cognition.BannonCambridgeAnalyticaInfluenceInfrastructureExact as Cambridge
import DASHI.Cognition.BannonCambridgeAnalyticaSystemicLeverageBridgeExact as CambridgeSystemic

------------------------------------------------------------------------
-- TRUMP / MAR-A-LAGO / BANNON BRIDGE
--
-- This owner strengthens the Trump-world acquisition lane with separately typed
-- infrastructures:
--   (1) Mar-a-Lago as an Epstein/Maxwell recruitment and records locus;
--   (2) Steve Bannon as a later political/media brokerage bridge to Epstein;
--   (3) Bannon's earlier Cambridge-Analytica/SCL/Mercer influence infrastructure.
-- The historical Bannon continuity is acquisition-relevant but does not prove
-- that Cambridge Analytica techniques were used in later Epstein media work.
-- The 2022 classified-documents search remains a distinct investigation absent
-- a document paying an Epstein-search purpose or seized-Epstein-material edge.
------------------------------------------------------------------------

data BridgeKind : Set where
  giuffreEmploymentAtMarALago : BridgeKind
  maxwellRecruitmentAtMarALago : BridgeKind
  maxwellTrialSubpoenaToMarALago : BridgeKind
  marALagoEmploymentRecordProduction : BridgeKind
  reinhartPriorEpsteinEmployeeRepresentation : BridgeKind
  classifiedDocumentsSearch : BridgeKind
  bannonCambridgeAnalyticaInfluenceInfrastructure : BridgeKind
  bannonSustainedCorrespondence : BridgeKind
  bannonEpsteinMediaRehabilitation : BridgeKind
  epsteinBannonPoliticalMessaging : BridgeKind
  bannonFarRightInternationalStrategy : BridgeKind

record BridgeReceipt : Set where
  constructor bridge-receipt
  field
    kind : BridgeKind
    sourceDescription : String
    relationshipOrInstitutionalEdgePaid : Bool
    directPrimaryOrOfficialRecord : Bool
    wrongdoingEstablishedByThisReceipt : Bool
    sameObjectWithOtherInvestigationEstablished : Bool
open BridgeReceipt public

giuffreEmploymentReceipt : BridgeReceipt
giuffreEmploymentReceipt = bridge-receipt
  giuffreEmploymentAtMarALago
  "DOJ-hosted Giuffre v Maxwell filings record that Giuffre obtained Mar-a-Lago employment records showing she worked there in 2000 while under 18."
  true true false false

maxwellRecruitmentReceipt : BridgeReceipt
maxwellRecruitmentReceipt = bridge-receipt
  maxwellRecruitmentAtMarALago
  "Giuffre's sentencing statement in United States v Maxwell states that Maxwell approached her at Mar-a-Lago in summer 2000 and procured her for Epstein; the statement is a victim account presented to the sentencing court."
  true true false false

marALagoSubpoenaReceipt : BridgeReceipt
marALagoSubpoenaReceipt = bridge-receipt
  maxwellTrialSubpoenaToMarALago
  "DOJ EFTA court subpoena dated October 5, 2021 commanded the Mar-a-Lago Club to appear in United States v Maxwell and produce specified employment records."
  true true false false

employmentRecordProductionReceipt : BridgeReceipt
employmentRecordProductionReceipt = bridge-receipt
  marALagoEmploymentRecordProduction
  "Giuffre v Maxwell discovery records expressly sought all documents concerning Giuffre's Mar-a-Lago employment/association and identified Mar-a-Lago among employers whose records were requested."
  true true false false

reinhartReceipt : BridgeReceipt
reinhartReceipt = bridge-receipt
  reinhartPriorEpsteinEmployeeRepresentation
  "Public reporting documents that magistrate judge Bruce Reinhart, before joining the bench, represented some Epstein employees; this historical legal-services relationship does not make the 2022 search an Epstein investigation."
  true false false false

classifiedSearchReceipt : BridgeReceipt
classifiedSearchReceipt = bridge-receipt
  classifiedDocumentsSearch
  "The August 2022 Mar-a-Lago search concerned presidential/classified records and obstruction-related offences; available warrants/FOIA records do not establish an Epstein-search purpose."
  true true false false

bannonCambridgeAnalyticaReceipt : BridgeReceipt
bannonCambridgeAnalyticaReceipt = bridge-receipt
  bannonCambridgeAnalyticaInfluenceInfrastructure
  "UK Parliament, FTC and FEC records establish Bannon's Cambridge Analytica leadership/infrastructure context, deceptive Facebook-data harvesting for voter profiling/targeting, substantial Trump-campaign vendor payments and cross-Atlantic brokerage; election-outcome causation and illegal common-vendor coordination remain unestablished by the current receipt set."
  true true false false

bannonCorrespondenceReceipt : BridgeReceipt
bannonCorrespondenceReceipt = bridge-receipt
  bannonSustainedCorrespondence
  "House-released/DOJ-era reporting documents sustained 2018-2019 Epstein-Bannon correspondence; Guardian's 2026 visualization reports nearly 1,500 emails between them or their assistants."
  true false false false

bannonMediaRehabReceipt : BridgeReceipt
bannonMediaRehabReceipt = bridge-receipt
  bannonEpsteinMediaRehabilitation
  "Released texts and video show Bannon advising Epstein on media presentation and filming extensive interview material reportedly intended for a documentary about Epstein."
  true false false false

bannonPoliticalMessagingReceipt : BridgeReceipt
bannonPoliticalMessagingReceipt = bridge-receipt
  epsteinBannonPoliticalMessaging
  "Released 2018 messages show Epstein advising Bannon during a pro-Trump media campaign while Bannon simultaneously advised Epstein on media/legal reputation strategy."
  true false false false

bannonInternationalStrategyReceipt : BridgeReceipt
bannonInternationalStrategyReceipt = bridge-receipt
  bannonFarRightInternationalStrategy
  "2026 reporting on released files describes Bannon seeking Epstein support/funding in relation to European right-populist political efforts; exact completed funding edges remain separately receipt-dependent."
  true false false false

------------------------------------------------------------------------
-- Bannon historical influence cross-pollination.
------------------------------------------------------------------------

bannonHistoricalInfluenceBoundary : Cambridge.BannonInfluenceInfrastructureBoundary
bannonHistoricalInfluenceBoundary = Cambridge.canonicalBannonInfluenceInfrastructureBoundary

bannonSystemicInfluenceBoundary : CambridgeSystemic.CambridgeAnalyticaSystemicBoundary
bannonSystemicInfluenceBoundary = CambridgeSystemic.canonicalCambridgeAnalyticaSystemicBoundary

bannonTargetedInfluenceCapabilityPaid :
  Cambridge.targetedPoliticalInfluenceCapabilityPaid
    Cambridge.canonicalBannonInfluenceInfrastructureBoundary ≡ true
bannonTargetedInfluenceCapabilityPaid = refl

bannonElectionOutcomeCausationStillUnpaid :
  Cambridge.trumpVictoryCausedByCambridgeAnalytica
    Cambridge.canonicalBannonInfluenceInfrastructureBoundary ≡ false
bannonElectionOutcomeCausationStillUnpaid = refl

bannonLaterEpsteinTechniqueReuseStillUnpaid :
  Cambridge.laterEpsteinMediaWorkProvesTechniqueReuse
    Cambridge.canonicalBannonInfluenceInfrastructureBoundary ≡ false
bannonLaterEpsteinTechniqueReuseStillUnpaid = refl

bannonThirdOrderSystemicAcquisitionStillOpen :
  CambridgeSystemic.laterEpsteinTechniqueReuseResolved
    CambridgeSystemic.canonicalCambridgeAnalyticaSystemicBoundary ≡ false
bannonThirdOrderSystemicAcquisitionStillOpen = refl

------------------------------------------------------------------------
-- Participation/status refinement.
------------------------------------------------------------------------

record TrumpParticipationLatticeBoundary : Set where
  constructor trump-participation-lattice-boundary
  field
    socialParticipationEstablished : Bool
    networkAccessParticipationEstablished : Bool
    marALagoRecruitmentLocusEstablished : Bool
    bannonHistoricalInfluenceInfrastructureEstablished : Bool
    knowledgeOfEpsteinCrimesResolved : Bool
    facilitationOfEpsteinCrimesEstablished : Bool
    criminalParticipationEstablishedByCurrentReceiptSet : Bool
open TrumpParticipationLatticeBoundary public

canonicalTrumpParticipationLatticeBoundary : TrumpParticipationLatticeBoundary
canonicalTrumpParticipationLatticeBoundary =
  trump-participation-lattice-boundary true true true true false false false

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data RecruitmentLocusImpliesOwnerKnowledge : Set where
data PriorRepresentationImpliesSearchPurpose : Set where
data SamePropertyImpliesSameInvestigation : Set where
data BannonBridgeImpliesTrumpDirection : Set where
data BannonEpsteinContactImpliesCriminalParticipation : Set where
data VictimAccountImpliesEveryAdjacentActorKnowledge : Set where
data PriorInfluenceInfrastructureImpliesLaterTechniqueReuse : Set where

recruitmentLocusDoesNotCreateOwnerKnowledge : RecruitmentLocusImpliesOwnerKnowledge → ⊥
recruitmentLocusDoesNotCreateOwnerKnowledge ()

priorRepresentationDoesNotCreateSearchPurpose : PriorRepresentationImpliesSearchPurpose → ⊥
priorRepresentationDoesNotCreateSearchPurpose ()

samePropertyDoesNotCreateSameInvestigation : SamePropertyImpliesSameInvestigation → ⊥
samePropertyDoesNotCreateSameInvestigation ()

bannonBridgeDoesNotCreateTrumpDirection : BannonBridgeImpliesTrumpDirection → ⊥
bannonBridgeDoesNotCreateTrumpDirection ()

bannonContactDoesNotCreateCriminalParticipation : BannonEpsteinContactImpliesCriminalParticipation → ⊥
bannonContactDoesNotCreateCriminalParticipation ()

victimAccountDoesNotCreateAdjacentKnowledge : VictimAccountImpliesEveryAdjacentActorKnowledge → ⊥
victimAccountDoesNotCreateAdjacentKnowledge ()

priorInfluenceInfrastructureDoesNotCreateLaterTechniqueReuse :
  PriorInfluenceInfrastructureImpliesLaterTechniqueReuse → ⊥
priorInfluenceInfrastructureDoesNotCreateLaterTechniqueReuse ()


------------------------------------------------------------------------
-- BANNON / EPSTEIN FILM ORIGINAL-OBJECT RECONCILIATION — 2026-10-24
--
-- Prior media/correspondence receipt ABOVE already pays existence of
-- filming and reputation-management interactions. Do NOT duplicate that
-- fact as a fresh discovery in a parallel Aquino-specific source model.
--
-- An indexed DOJ-produced April 3 2019 engagement letter and an original
-- House-Oversight iMessage export sharpen *production terms* and *shooting
-- schedule*. They do not determine whether Bannon signed the letter,
-- attorney-client or Kovel privilege was legally effective, whether the
-- terms covered any named released video segment, or final ownership.
-- Neither record supplies knowledge or participation in abuse.
------------------------------------------------------------------------

data BannonProductionArtifact : Set where
  actualInterviewFootagePreviouslyKnown : BannonProductionArtifact
  april2019IndykeLetter : BannonProductionArtifact
  juneJuly2019ProductionMessages : BannonProductionArtifact

record BannonProductionEvidence : Set where
  constructor bannon-production-evidence
  field
    artifact : BannonProductionArtifact
    sourceLocator : String
    narrowSupportedFinding : String
    documentarySourceTextLocated : Bool
    originalPageImageInspectedThisCut : Bool
    signedOrExecutedAgreementEstablished : Bool
    legalPrivilegeEffectivenessEstablished : Bool
    sameReleasedFilmReelIdentified : Bool
    originalVideoHashOrProductionManifestHeld : Bool
    espionageOrCriminalParticipationPaid : Bool
open BannonProductionEvidence public

existingFilmEvidence : BannonProductionEvidence
existingFilmEvidence = bannon-production-evidence
  actualInterviewFootagePreviouslyKnown
  "Existing bannonMediaRehabReceipt and released 2026 news/DOJ video coverage"
  "Released text and video already source-bounded in this owner; no new proof of filming needed."
  true false false false false false false

indyke2019LetterEvidence : BannonProductionEvidence
indyke2019LetterEvidence = bannon-production-evidence
  april2019IndykeLetter
  "DOJ Dataset 9 EFTA00809863-EFTA00809866, April 3 2019; https://www.justice.gov/epstein/files/DataSet%209/EFTA00809863.pdf"
  "DOJ-indexed four-page lawyer letter addressed to Bannon describes consultant litigation support, confidentiality and putative Indyke control/ownership of resulting video or other materials; extracted text inspected via public EFTA mirror. PDF page images, handwritten/actual execution, later assent and enforceability NOT inspected or established."
  true false false false false false false

juneJulyProductionMessagesEvidence : BannonProductionEvidence
juneJulyProductionMessagesEvidence = bannon-production-evidence
  juneJuly2019ProductionMessages
  "House Oversight 027794-027848 iMessage export, https://media-cdn.rollcall.com/epstein-files/House_Oversight_027794-027847.pdf"
  "PDF inspected: 15 June 2019 shooting subject-expert and crew discussions; 6 July 2019 03:59 proposed island filming and reply yes; 16:37 Epstein says All canceled. Planning and cancellation are paid; a resulting completed island shoot is NOT paid."
  true true false false false false false

-- Only the earlier broad fact of filming is an established bounded
-- relationship. These additional artefacts pay proposed terms and planning.
bannonFilmingAlreadyPaid :
  relationshipOrInstitutionalEdgePaid bannonMediaRehabReceipt ≡ true
bannonFilmingAlreadyPaid = refl

noNewProofNeededThatVideoExists :
  documentarySourceTextLocated existingFilmEvidence ≡ true
noNewProofNeededThatVideoExists = refl

letterLocatedButExecutionOpen :
  signedOrExecutedAgreementEstablished indyke2019LetterEvidence ≡ false
letterLocatedButExecutionOpen = refl

letterCannotByItselfCreateLegalPrivilege :
  legalPrivilegeEffectivenessEstablished indyke2019LetterEvidence ≡ false
letterCannotByItselfCreateLegalPrivilege = refl

july6ProposedShootNotCompletedShoot :
  sameReleasedFilmReelIdentified juneJulyProductionMessagesEvidence ≡ false
july6ProposedShootNotCompletedShoot = refl

letterAndMessageDoNotIdentifyFilmReel :
  sameReleasedFilmReelIdentified indyke2019LetterEvidence ≡ false
letterAndMessageDoNotIdentifyFilmReel = refl

-- Scope the actual remaining work to original reel/production file,
-- executed counsel agreement, and same-session join, rather than the
-- already-paid premise that extensive filming occurred.
record BannonMediaProductionFrontier : Set where
  constructor bannon-media-production-frontier
  field
    releasedInterviewExistencePaid : Bool
    engagementLetterTextLocated : Bool
    july6ProductionPlanningMessagesLocated : Bool
    originalCounselLetterSignatureVerified : Bool
    specificVideoReelFileIdAndHashVerified : Bool
    counselLetterCoversReleasedReel : Bool
    contemporaneousFilmingSessionJoinedToMessage : Bool
    concludedIntelligenceOrBlackmailOperation : Bool
open BannonMediaProductionFrontier public

canonicalBannonMediaProductionFrontier : BannonMediaProductionFrontier
canonicalBannonMediaProductionFrontier = bannon-media-production-frontier
  true true true false false false false false

videoExistenceDebtRetired :
  releasedInterviewExistencePaid canonicalBannonMediaProductionFrontier ≡ true
videoExistenceDebtRetired = refl

exactFilmReelObjectStillUnpaid :
  specificVideoReelFileIdAndHashVerified canonicalBannonMediaProductionFrontier ≡ false
exactFilmReelObjectStillUnpaid = refl

legalEngagementCannotBePromotedToExecuted :
  originalCounselLetterSignatureVerified canonicalBannonMediaProductionFrontier ≡ false
legalEngagementCannotBePromotedToExecuted = refl

filmCannotBePromotedToIntelligenceDirection :
  concludedIntelligenceOrBlackmailOperation canonicalBannonMediaProductionFrontier ≡ false
filmCannotBePromotedToIntelligenceDirection = refl

------------------------------------------------------------------------
-- MINIMAL VIDEO PROVENANCE RECEIPT: HASH / TIMECODE / TRANSCRIPT
-- NO VIDEO FILES IN THIS REPOSITORY.
--
-- Original/released object identity and SHA-256 of a specific third-party
-- rendition are DISTINCT; re-encoding changes a cryptographic digest.
-- Two YouTube uploads are source *locators*, not proof of matching bytes.
-- Third-party chapter descriptions are NOT a verbatim timecoded transcript.
------------------------------------------------------------------------

record LightweightFilmObjectReceipt : Set where
  constructor lightweight-film-object-receipt
  field
    declaredManifest : String
    publicRenditionLocator : String
    vendorFullFilmRequiredForAnalysis : Bool
    publicRenditionSHA256ComputedHere : Bool
    dojNativeMasterSHA256ComputedHere : Bool
    transcriptTextAcquired : Bool
    thirdPartyChapterIndexLocated : Bool
    chapterIndexIsVerbatimTranscript : Bool
    namedReelToContractAndShootJoined : Bool
open LightweightFilmObjectReceipt public

canonicalLightweightFilmObjectReceipt : LightweightFilmObjectReceipt
canonicalLightweightFilmObjectReceipt = lightweight-film-object-receipt
  "docs/research/bannon-epstein-video-manifest-20261024.json"
  "DOJ Data Set 10 EFTA01600824.mov plus separate 2026-02-01 third-party YouTube re-encodes"
  false false false false true false false

videoNeedNotBeVendored :
  vendorFullFilmRequiredForAnalysis canonicalLightweightFilmObjectReceipt ≡ false
videoNeedNotBeVendored = refl

noUncomputedSHA256Fabrication :
  publicRenditionSHA256ComputedHere canonicalLightweightFilmObjectReceipt ≡ false
noUncomputedSHA256Fabrication = refl

chapterTimestampsNotVerbatimTranscript :
  chapterIndexIsVerbatimTranscript canonicalLightweightFilmObjectReceipt ≡ false
chapterTimestampsNotVerbatimTranscript = refl

noTranscriptClaimWithoutBytes :
  transcriptTextAcquired canonicalLightweightFilmObjectReceipt ≡ false
noTranscriptClaimWithoutBytes = refl

reelToAgreementJoinNotConferredByHash :
  namedReelToContractAndShootJoined canonicalLightweightFilmObjectReceipt ≡ false
reelToAgreementJoinNotConferredByHash = refl

------------------------------------------------------------------------
-- EXACT DOJ ORIGINAL REEL IDENTIFIER + TRANSCRIPT LOCATORS LOCATED
-- 2026-10-24. This retires *identifier discovery*, NOT content hashing.
------------------------------------------------------------------------

record LocatedVideoTranscriptIndex : Set where
  constructor located-video-transcript-index
  field
    dojReelObjectId : String
    dojMediaURL : String
    thirdPartyTimecodedTranscriptURL : String
    originalDOJReelIdentifierLocated : Bool
    sourceVideoContentDigestVerified : Bool
    thirdPartyTimecodedTranscriptLocated : Bool
    transcriptManuallyVerifiedAgainstReel : Bool
    mayConfuseTwoIndependentASROutputsWithTwoMediaSources : Bool
    april2019CounselAgreementIdentifiedToThisReel : Bool
open LocatedVideoTranscriptIndex public

bannonOriginalReelIndex : LocatedVideoTranscriptIndex
bannonOriginalReelIndex = located-video-transcript-index
  "EFTA01600824"
  "https://www.justice.gov/epstein/files/DataSet%2010/EFTA01600824.mov"
  "https://www.tommycarstensen.com/epstein/data/transcripts/EFTA01600824.html"
  true false true false false false

dojReelIdentifierLocated :
  originalDOJReelIdentifierLocated bannonOriginalReelIndex ≡ true
dojReelIdentifierLocated = refl

publishedTimecodedTranscriptLocated :
  thirdPartyTimecodedTranscriptLocated bannonOriginalReelIndex ≡ true
publishedTimecodedTranscriptLocated = refl

dojReelHashStillUncomputed :
  sourceVideoContentDigestVerified bannonOriginalReelIndex ≡ false
dojReelHashStillUncomputed = refl

transcriptWithoutReviewNotCertified :
  transcriptManuallyVerifiedAgainstReel bannonOriginalReelIndex ≡ false
transcriptWithoutReviewNotCertified = refl

originalReelIdDoesNotPay2019ContractJoin :
  april2019CounselAgreementIdentifiedToThisReel bannonOriginalReelIndex ≡ false
originalReelIdDoesNotPay2019ContractJoin = refl

------------------------------------------------------------------------
-- TRANSCRIPT-FIRST CONTENT AUDIT (EFTA01600824, 2026-10-24)
--
-- Research acceptance: a located timecoded ASR transcript is sufficient
-- for source-bounded scene and attributed-statement analysis. Optional
-- byte SHA-256 is NOT a blocker. ASR's machine speaker labels and its
-- paraphrases cannot authenticate off-screen identities, financial facts,
-- or a separate Black/Apollo or Aquino intelligence programme.
------------------------------------------------------------------------

data InterviewStatementRole : Set where
  filmProductionDirection : InterviewStatementRole
  attributedFinancialOrScientificClaim : InterviewStatementRole
  interviewerQuestionNotHistoricalFinding : InterviewStatementRole
  contemporaryAccountNeedsExternalDateAudit : InterviewStatementRole
  genericNamedAssociation : InterviewStatementRole

record TimecodedTranscriptReceipt : Set where
  constructor timecoded-transcript-receipt
  field
    timeStart : String
    timeEnd : String
    source : String
    role : InterviewStatementRole
    boundedContent : String
    timecodedTextLocated : Bool
    underlyingHistoricalClaimVerified : Bool
    newDirectLeonBlackAgreementPaid : Bool
    anyIntelligenceCommandPaid : Bool
open TimecodedTranscriptReceipt public

stagedOffCameraInterview : TimecodedTranscriptReceipt
stagedOffCameraInterview = timecoded-transcript-receipt
  "00:00:14" "00:00:34"
  "EFTA01600824 third-party timecoded ASR transcript opening"
  filmProductionDirection
  "Off-camera interviewer's questions were not intended to be heard in the polished presentation; interlocutors discuss recording both ways and restating prompts. This supports intentional staged interview instructions, not final editorial execution or legal copyright ownership."
  true false false false

rockefellerAccessNarrative : TimecodedTranscriptReceipt
rockefellerAccessNarrative = timecoded-transcript-receipt
  "00:00:53" "00:05:30"
  "EFTA01600824 ASR; first-person Rockefeller University/Trilateral self-description"
  attributedFinancialOrScientificClaim
  "Epstein gives self-attributed recollections about Rockefeller University institutional ties, David Rockefeller and finance/institutional access. Such recollection is a participant statement, not a board roster or an independently verified appointment."
  true false false false

mercerSurnameReference : TimecodedTranscriptReceipt
mercerSurnameReference = timecoded-transcript-receipt
  "00:10:07" "00:10:22"
  "EFTA01600824 ASR, surname Mercer in a banking analogy"
  genericNamedAssociation
  "Transcript has Epstein addressing Bannon about his old boss Mercer and understanding of banking. A surname reference does not document a new Bannon-Mercer-Epstein contract, does not identify Robert Maxwell, and does not transfer CA datasets."
  true false false false

aiAsComplexityNarrative : TimecodedTranscriptReceipt
aiAsComplexityNarrative = timecoded-transcript-receipt
  "00:22:52" "00:24:31"
  "EFTA01600824 ASR, neural networks and AI analogy"
  attributedFinancialOrScientificClaim
  "Participant explains contemporary neural networks and opaque decision making as an analogy to complexity. This is speech about AI, not a primary grant, code, investment, deployed dataset or programmatic command."
  true false false false

bearLehmanJailCallNarrative : TimecodedTranscriptReceipt
bearLehmanJailCallNarrative = timecoded-transcript-receipt
  "00:27:28" "00:37:43"
  "EFTA01600824 ASR juxtaposed with official FDIC 2000-2009 crisis history"
  contemporaryAccountNeedsExternalDateAudit
  "Epstein self-reports jail collect calls to Bear Stearns leadership and a JPMorgan contact after learning of financial crisis; ASR intermixes Bear acquisition and Lehman bankruptcy. FDIC places Bear acquisition in March 2008 and Lehman bankruptcy on September 15 2008. Exact dates/call logs and whether narration conflates events remain unpaid."
  true false false false

santaFeComplexityDonorNarrative : TimecodedTranscriptReceipt
santaFeComplexityDonorNarrative = timecoded-transcript-receipt
  "01:08:44" "01:13:38"
  "EFTA01600824 ASR, Santa Fe/Los Alamos research narrative"
  attributedFinancialOrScientificClaim
  "Epstein narrates Santa Fe research financing, Los Alamos scientists and computational complexity work. No original grant, university accounting entry, collaborator authorship or technical program transfer is verified by speech alone."
  true false false false

donorEthicsLegalityExchange : TimecodedTranscriptReceipt
donorEthicsLegalityExchange = timecoded-transcript-receipt
  "01:53:34" "01:55:40"
  "EFTA01600824 ASR, institutional donors and source-of-funds questioning"
  interviewerQuestionNotHistoricalFinding
  "Bannon's questioning of whether institutions should accept Epstein's funding and responses claiming lawful earnings record competing rhetorical positions. Neither speaker's self-justification nor the question pays an external legal or financial finding."
  true false false false

canonicalTranscriptContentCuts : List TimecodedTranscriptReceipt
canonicalTranscriptContentCuts =
  stagedOffCameraInterview ∷ rockefellerAccessNarrative
  ∷ mercerSurnameReference ∷ aiAsComplexityNarrative
  ∷ bearLehmanJailCallNarrative ∷ santaFeComplexityDonorNarrative
  ∷ donorEthicsLegalityExchange ∷ []

record TranscriptResearchAcceptance : Set where
  constructor transcript-research-acceptance
  field
    existingExternalTimecodedASRIsSufficient : Bool
    researchRequiresMediaVendoring : Bool
    researchRequiresVideoSHA256 : Bool
    researcherInspectedOriginalVideoToVerifyASR : Bool
    externalTimecodesAndSourceRolesIndexed : Bool
    exactSceneConnectedToIndykeAgreement : Bool
    transcriptProvesBlackTransactions : Bool
open TranscriptResearchAcceptance public

canonicalTranscriptResearchAcceptance : TranscriptResearchAcceptance
canonicalTranscriptResearchAcceptance = transcript-research-acceptance
  true false false false true false false

transcriptSufficientForThisResearchCut :
  existingExternalTimecodedASRIsSufficient
    canonicalTranscriptResearchAcceptance ≡ true
transcriptSufficientForThisResearchCut = refl

videoHashNotAnAcceptanceGate :
  researchRequiresVideoSHA256 canonicalTranscriptResearchAcceptance ≡ false
videoHashNotAnAcceptanceGate = refl

verbatimTranscriptNotVendored :
  researchRequiresMediaVendoring canonicalTranscriptResearchAcceptance ≡ false
verbatimTranscriptNotVendored = refl

noBlackTransactionFromInterviewSpeech :
  transcriptProvesBlackTransactions canonicalTranscriptResearchAcceptance ≡ false
noBlackTransactionFromInterviewSpeech = refl

original2019AgreementNotProvenByNarrative :
  exactSceneConnectedToIndykeAgreement canonicalTranscriptResearchAcceptance ≡ false
original2019AgreementNotProvenByNarrative = refl

------------------------------------------------------------------------
-- SFI / FDIC HISTORICAL SOURCE CALIBRATION.
-- Government and institutional records are independent of the interview's
-- self-claims; a later donor is not necessarily a founding scientist, and
-- date mismatches require careful event decomposition, not guilt inference.
------------------------------------------------------------------------

record HistoricalSourceComparator : Set where
  constructor historical-source-comparator
  field
    sourceURL : String
    historicalFinding : String
    originalInstitutionalOrRegulatorAuthor : Bool
    confirmsEpsteinPersonalDonorOrCallClaim : Bool
    dischargesAnyCommonIntelligenceCommand : Bool
open HistoricalSourceComparator public

santaFeOfficialHistory : HistoricalSourceComparator
santaFeOfficialHistory = historical-source-comparator
  "https://www.santafe.edu/about/history"
  "Institutional history says George Cowan's group developed the institute in 1982-1984, incorporated May 1984, first workshops autumn 1984; early 1990s support cannot prove original foundation in 1984."
  true false false

fdic2008OriginalTimeline : HistoricalSourceComparator
fdic2008OriginalTimeline = historical-source-comparator
  "https://www.fdic.gov/history/2000-2009"
  "FDIC dates JPMorgan acquisition of Bear Stearns to March 24 2008 and Lehman bankruptcy to September 15 2008; a retold collect-call story combining these stages requires exact call-date logs and chronology reconciliation."
  true false false

epsteinSelfBiographicalRecord : HistoricalSourceComparator
epsteinSelfBiographicalRecord = historical-source-comparator
  "https://yirah.fi/epstein/en/document/EFTA00304519"
  "DOJ-recorded one-page promotional biography EFTA00304519 claims former Rockefeller board service and Santa Fe support. It is a source for self-presentation, NOT independent verification of appointments, charitable expenditure or programme governance."
  false false false

early1990sSFIClaimIsNot1984Founding :
  confirmsEpsteinPersonalDonorOrCallClaim santaFeOfficialHistory ≡ false
early1990sSFIClaimIsNot1984Founding = refl

officialFinancialTimelineIsNotJailCallLog :
  confirmsEpsteinPersonalDonorOrCallClaim fdic2008OriginalTimeline ≡ false
officialFinancialTimelineIsNotJailCallLog = refl

promotionalBioNotIndependentInstitution :
  originalInstitutionalOrRegulatorAuthor epsteinSelfBiographicalRecord ≡ false
promotionalBioNotIndependentInstitution = refl
