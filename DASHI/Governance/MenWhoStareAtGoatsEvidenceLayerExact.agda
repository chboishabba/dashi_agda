module DASHI.Governance.MenWhoStareAtGoatsEvidenceLayerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- MEN WHO STARE AT GOATS: EVIDENCE-LAYER BOUNDARY
--
-- Source-bounded finite epistemic geometry.  This owner distinguishes:
--
--   documented programme / document existence
--   participant or investigative narrative
--   experimental/session report
--   programme-level efficacy evaluation
--   journalistic reconstruction
--   fictionalised/satirical screen representation
--
-- It does NOT prove paranormal efficacy, goat-killing by psychic means, or the
-- literal truth of every event in a journalistic or film narrative.
------------------------------------------------------------------------

data GoatsClaimKind : Set where
  programmeExistedClaim
  remoteViewingSessionOccurredClaim
  extraordinaryEffectClaim
  intelligenceUtilityClaim
  goatKillingByStaringClaim
  institutionalInterestClaim
  : GoatsClaimKind

data EvidenceLayer : Set where
  declassifiedInstitutionalRecord
  sessionReport
  programmeEvaluation
  participantTestimony
  investigativeJournalism
  publisherNarrative
  dramatizedFilm
  : EvidenceLayer

data SupportStatus : Set where
  documented
  sourceReports
  disputedOrUnresolved
  notEstablishedHere
  : SupportStatus

record GoatsEvidenceReceipt : Set where
  constructor goatsEvidenceReceipt
  field
    claim : GoatsClaimKind
    layer : EvidenceLayer
    status : SupportStatus
    sourceReference : String
    scopeNote : String

open GoatsEvidenceReceipt public

------------------------------------------------------------------------
-- Exact source-role fixtures.
------------------------------------------------------------------------

stargateProgrammeRecord : GoatsEvidenceReceipt
stargateProgrammeRecord = goatsEvidenceReceipt
  programmeExistedClaim
  declassifiedInstitutionalRecord
  documented
  "CIA STAR GATE / remote-viewing declassified record collection"
  "documents programme existence and records; does not establish paranormal efficacy"

remoteViewingSessionRecord : GoatsEvidenceReceipt
remoteViewingSessionRecord = goatsEvidenceReceipt
  remoteViewingSessionOccurredClaim
  sessionReport
  documented
  "CIA FOIA GRILL FLAME remote-viewing session reports"
  "documents that sessions occurred and what was reported during them"

programmeUtilityEvaluation : GoatsEvidenceReceipt
programmeUtilityEvaluation = goatsEvidenceReceipt
  intelligenceUtilityClaim
  programmeEvaluation
  notEstablishedHere
  "1995 independent evaluation / subsequent CIA programme decision"
  "programme was not restored for intelligence use; existence of anomalous reports is not operational utility"

ronsonGoatNarrative : GoatsEvidenceReceipt
ronsonGoatNarrative = goatsEvidenceReceipt
  goatKillingByStaringClaim
  investigativeJournalism
  sourceReports
  "Jon Ronson, The Men Who Stare at Goats"
  "journalistic narrative is retained as a source claim, not promoted here into experimental proof"

publisherGoatNarrative : GoatsEvidenceReceipt
publisherGoatNarrative = goatsEvidenceReceipt
  goatKillingByStaringClaim
  publisherNarrative
  sourceReports
  "Simon & Schuster publisher description of The Men Who Stare at Goats"
  "marketing/summary surface is not independent empirical verification"

------------------------------------------------------------------------
-- Same extraordinary public story can hide different evidential standing.
------------------------------------------------------------------------

data PublicGoatsSurface : Set where
  sameGoatsStorySurface : PublicGoatsSurface

data EvidentialWorld : Set where
  institutionalProgrammeWorld
  narratedExtraordinaryWorld
  : EvidentialWorld

publicSurface : EvidentialWorld → PublicGoatsSurface
publicSurface _ = sameGoatsStorySurface

claimStanding : EvidentialWorld → SupportStatus
claimStanding institutionalProgrammeWorld = documented
claimStanding narratedExtraordinaryWorld = sourceReports

sameSurface : publicSurface institutionalProgrammeWorld ≡ publicSurface narratedExtraordinaryWorld
sameSurface = refl

standingDiffers :
  claimStanding institutionalProgrammeWorld ≡ claimStanding narratedExtraordinaryWorld → ⊥
standingDiffers ()

publicStoryCannotRecoverEvidenceStanding :
  INF.FactorsThrough publicSurface claimStanding → ⊥
publicStoryCannotRecoverEvidenceStanding =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      institutionalProgrammeWorld
      narratedExtraordinaryWorld
      refl
      standingDiffers)

------------------------------------------------------------------------
-- Promotion gates.
------------------------------------------------------------------------

data ProgrammeExistencePromotesParanormalEfficacy : Set where

data SessionReportPromotesOperationalUtility : Set where

data ParticipantTestimonyPromotesExperimentalProof : Set where

data JournalismPromotesDeclassifiedInstitutionalFact : Set where

data FilmPromotesHistoricalFact : Set where

data GoatNarrativePromotesPsychicGoatKillingProof : Set where

programmeExistenceDoesNotPromoteParanormalEfficacy :
  ProgrammeExistencePromotesParanormalEfficacy → ⊥
programmeExistenceDoesNotPromoteParanormalEfficacy ()

sessionReportDoesNotPromoteOperationalUtility :
  SessionReportPromotesOperationalUtility → ⊥
sessionReportDoesNotPromoteOperationalUtility ()

participantTestimonyDoesNotPromoteExperimentalProof :
  ParticipantTestimonyPromotesExperimentalProof → ⊥
participantTestimonyDoesNotPromoteExperimentalProof ()

journalismDoesNotPromoteDeclassifiedFact :
  JournalismPromotesDeclassifiedInstitutionalFact → ⊥
journalismDoesNotPromoteDeclassifiedFact ()

filmDoesNotPromoteHistoricalFact : FilmPromotesHistoricalFact → ⊥
filmDoesNotPromoteHistoricalFact ()

goatNarrativeDoesNotPromotePsychicGoatKillingProof :
  GoatNarrativePromotesPsychicGoatKillingProof → ⊥
goatNarrativeDoesNotPromotePsychicGoatKillingProof ()

------------------------------------------------------------------------
-- BIDI source demand: each consumer asks for a source layer adequate to the
-- claim it wants to promote.
------------------------------------------------------------------------

data EvidenceDemand : GoatsClaimKind → Set where
  programmeExistenceNeedsInstitutionalRecord :
    EvidenceDemand programmeExistedClaim
  sessionOccurrenceNeedsSessionRecord :
    EvidenceDemand remoteViewingSessionOccurredClaim
  extraordinaryEffectNeedsControlledEvidence :
    EvidenceDemand extraordinaryEffectClaim
  intelligenceUtilityNeedsProgrammeEvaluation :
    EvidenceDemand intelligenceUtilityClaim
  goatKillingNeedsIndependentExperimentalEvidence :
    EvidenceDemand goatKillingByStaringClaim
  institutionalInterestNeedsInstitutionalHistory :
    EvidenceDemand institutionalInterestClaim

canonicalGoatClaimDemand : EvidenceDemand goatKillingByStaringClaim
canonicalGoatClaimDemand = goatKillingNeedsIndependentExperimentalEvidence

record MenWhoStareAtGoatsEvidenceBoundary : Set where
  constructor menWhoStareAtGoatsEvidenceBoundary
  field
    programmeExistenceIsDocumented : Bool
    programmeExistenceIsDocumentedIsTrue : programmeExistenceIsDocumented ≡ true
    programmeExistenceProvesParanormalEfficacy : Bool
    programmeExistenceProvesParanormalEfficacyIsFalse :
      programmeExistenceProvesParanormalEfficacy ≡ false
    journalismAloneProvesGoatKillingMechanism : Bool
    journalismAloneProvesGoatKillingMechanismIsFalse :
      journalismAloneProvesGoatKillingMechanism ≡ false
    filmIsHistoricalProof : Bool
    filmIsHistoricalProofIsFalse : filmIsHistoricalProof ≡ false
    sourceLayerMustMatchConsumer : Bool
    sourceLayerMustMatchConsumerIsTrue : sourceLayerMustMatchConsumer ≡ true

canonicalMenWhoStareAtGoatsEvidenceBoundary : MenWhoStareAtGoatsEvidenceBoundary
canonicalMenWhoStareAtGoatsEvidenceBoundary =
  menWhoStareAtGoatsEvidenceBoundary
    true refl false refl false refl false refl true refl
