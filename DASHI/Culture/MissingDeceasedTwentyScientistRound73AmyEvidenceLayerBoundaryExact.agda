module DASHI.Culture.MissingDeceasedTwentyScientistRound73AmyEvidenceLayerBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Governance.MenWhoStareAtGoatsEvidenceLayerExact as Goats
import DASHI.Culture.MissingDeceasedTwentyScientistRound72AmyRichardPOAMSCandidateWeldExact as R72

------------------------------------------------------------------------
-- ROUND 73: AMY EVIDENCE-LAYER BOUNDARY
--
-- Cross-pollinates the Men Who Stare at Goats evidence-layer formalism into
-- the Amy/Richard/POAMS referent problem.  Same public story / thematic fit
-- cannot recover evidentiary standing.  The source layer must match the claim
-- consumer.
------------------------------------------------------------------------

data AmyEvidenceLayer : Set where
  archivedSelfReport : AmyEvidenceLayer
  institutionalPresentation : AmyEvidenceLayer
  institutionalTechnicalRecord : AmyEvidenceLayer
  derivativeJournalism : AmyEvidenceLayer
  laterFolkloreRetelling : AmyEvidenceLayer

record AmyLayerReceipt : Set where
  constructor amy-layer-receipt
  field
    layer : AmyEvidenceLayer
    sourceReference : String
    pays : String
    doesNotPay : String

open AmyLayerReceipt public

amyArchivedStatement : AmyLayerReceipt
amyArchivedStatement = amy-layer-receipt
  archivedSelfReport
  "Wayback capture of Alien_Scientist post 2020-09-18 preserving screenshot attributed to Amy Eskridge"
  "Amy-attributed self-report that foundational work came from an unnamed team member while a NASA MSFC civil servant and that an unnamed paper was under NASA publication review"
  "authentication of an Amy-origin original message; identity of the unnamed team member; title/document ID of the paper; NASA review receipt; same-paper identity"

hal5TeamSurface : AmyLayerReceipt
hal5TeamSurface = amy-layer-receipt
  institutionalPresentation
  "HAL5 December 2018 presentation / programme surface"
  "Richard Eskridge appears on Amy's team surface and is described as retired NASA engineer/scientist / Professor Emeritus"
  "that Richard is the unnamed 2020 referent; that the 2018 deck experimentally validates extraordinary propulsion claims"

poamsNTRS : AmyLayerReceipt
poamsNTRS = amy-layer-receipt
  institutionalTechnicalRecord
  "NASA NTRS 20205010911 / NASA TM M-1531"
  "R.H. Eskridge, M.A. Nelson and M.P. Schoenfeld authored an MSFC technical memorandum; NTRS acquisition date 2020-12-01; POAMS paper identity and public NASA carrier"
  "that Amy referred to this paper in September 2020; that Amy authored it; that preliminary results establish an extraordinary propulsion mechanism"

derivativeAmyNarrative : AmyLayerReceipt
derivativeAmyNarrative = amy-layer-receipt
  derivativeJournalism
  "later articles/posts connecting Amy, Richard and POAMS"
  "existence of later public interpretations and candidate-link narratives"
  "institutional identity of the unnamed paper or team member; technical validation; suppression; causation"

folkloreAmyNarrative : AmyLayerReceipt
folkloreAmyNarrative = amy-layer-receipt
  laterFolkloreRetelling
  "later UFO/conspiracy retellings and social-media summaries"
  "that such narratives circulate"
  "NASA employment by Amy; Amy coauthorship on TM-20205010911; classified suppression; research-linked death; same-paper identity"

archivedSelfReportDoesNotPromoteInstitutionalRecord : Bool
archivedSelfReportDoesNotPromoteInstitutionalRecord = true

journalisticRetellingDoesNotPromoteSamePaperIdentity : Bool
journalisticRetellingDoesNotPromoteSamePaperIdentity = true

institutionalTechnicalRecordDoesNotIdentifyAmyReferentByItself : Bool
institutionalTechnicalRecordDoesNotIdentifyAmyReferentByItself = true

sameThematicStoryDoesNotEqualSameEvidenceLayer : Bool
sameThematicStoryDoesNotEqualSameEvidenceLayer = true

publicStoryCannotRecoverEvidenceStanding : Bool
publicStoryCannotRecoverEvidenceStanding = true

exactReferentNeedsIdentityBearingInstitutionalBridge : Bool
exactReferentNeedsIdentityBearingInstitutionalBridge = true

exactPaperIdentityNeedsTitleIdCitationOrReviewBridge : Bool
exactPaperIdentityNeedsTitleIdCitationOrReviewBridge = true

extraordinaryTechnicalClaimNeedsTechnicalEvidence : Bool
extraordinaryTechnicalClaimNeedsTechnicalEvidence = true

programmeOrPaperExistenceDoesNotPromoteExtraordinaryEfficacy : Bool
programmeOrPaperExistenceDoesNotPromoteExtraordinaryEfficacy = true

goatsBoundaryReused : Goats.MenWhoStareAtGoatsEvidenceBoundary
goatsBoundaryReused = Goats.canonicalMenWhoStareAtGoatsEvidenceBoundary

round73H2PaidCount : Nat
round73H2PaidCount = 0

round73H3PaidCount : Nat
round73H3PaidCount = 0

round73Reading : String
round73Reading = "The Amy/Richard/POAMS story must remain source-layered. Amy's archived statement is a self-report about an unnamed team member and unnamed NASA-reviewed paper. HAL5 pays Richard's presence on Amy's team surface. NASA NTRS pays the existence, authorship and chronology of TM-20205010911. Later articles and folklore preserve interpretations but cannot promote same-paper identity, extraordinary efficacy, suppression or causation. The live acquisition demand is therefore an identity-bearing institutional bridge: title/document ID, citation, correspondence, review receipt, release record or other source that explicitly connects Amy's 2020 statement to Richard Eskridge / POAMS."
