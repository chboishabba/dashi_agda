module DASHI.Cognition.TrumpEpsteinPoliticalRelationshipExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Governance.TrumpismDrugWarPsychedelicSemanticEpistemicCapstoneExact as Trumpism

------------------------------------------------------------------------
-- TRUMP <-> EPSTEIN POLITICAL / ELITE-ACCESS RELATIONSHIP OWNER
--
-- Historical relationship facts are kept separate from later Trumpism
-- interpretation machinery.  The governance capstone may contextualise policy
-- and narrative surfaces, but it cannot prove a historical Epstein edge.
------------------------------------------------------------------------

data TrumpEpsteinEdgeKind : Set where
  establishedSocialRelationship : TrumpEpsteinEdgeKind
  repeatedAirTravel : TrumpEpsteinEdgeKind
  marALagoRecruitmentLocus : TrumpEpsteinEdgeKind
  claimedClubBanReason : TrumpEpsteinEdgeKind
  birthdayBookSolicitation : TrumpEpsteinEdgeKind
  disputedBirthdayBookAuthorship : TrumpEpsteinEdgeKind
  epsteinKnowledgeClaim : TrumpEpsteinEdgeKind
  uncorroboratedFBIAllegation : TrumpEpsteinEdgeKind
  recordsReleaseGovernance : TrumpEpsteinEdgeKind

record TrumpEpsteinReceipt : Set where
  constructor trump-epstein-receipt
  field
    edgeKind : TrumpEpsteinEdgeKind
    sourceDescription : String
    historicalRelationshipEstablished : Bool
    directOrInstitutionalRecord : Bool
    wrongdoingEstablishedByThisReceipt : Bool
    contestedOrSourceAttributed : Bool
open TrumpEpsteinReceipt public

socialRelationshipReceipt : TrumpEpsteinReceipt
socialRelationshipReceipt = trump-epstein-receipt
  establishedSocialRelationship
  "Reuters/AP 2025-26 reporting based on released records describes Trump and Epstein as social acquaintances/friends in the 1990s and early 2000s; Trump says the association ended in the mid-2000s."
  true true false false

flightReceipt : TrumpEpsteinReceipt
flightReceipt = trump-epstein-receipt
  repeatedAirTravel
  "Reuters 2025 report on a DOJ-released January 2020 prosecutor email says flight records showed Trump flew on Epstein's private jet at least eight times in the 1990s, including at least four flights with Ghislaine Maxwell."
  true true false false

marALagoReceipt : TrumpEpsteinReceipt
marALagoReceipt = trump-epstein-receipt
  marALagoRecruitmentLocus
  "AP 2025: Trump acknowledged Epstein recruited young women who worked at the Mar-a-Lago spa, including Virginia Giuffre; Giuffre had long said Maxwell approached her while she worked there."
  true true false false

clubBanReasonReceipt : TrumpEpsteinReceipt
clubBanReasonReceipt = trump-epstein-receipt
  claimedClubBanReason
  "Trump's 2025 public account says he banned Epstein from Mar-a-Lago because Epstein repeatedly recruited/poached spa workers. This pays Trump's stated reason, not independent proof that it was the sole or actual motive."
  true true false true

birthdayBookSolicitationReceipt : TrumpEpsteinReceipt
birthdayBookSolicitationReceipt = trump-epstein-receipt
  birthdayBookSolicitation
  "2026 WSJ reporting on DOJ files says records show an effort in 2002 to solicit a Trump contribution to Epstein's 50th-birthday book; seized media later included copies of the birthday book."
  true true false false

birthdayBookAuthorshipDisputed : TrumpEpsteinReceipt
birthdayBookAuthorshipDisputed = trump-epstein-receipt
  disputedBirthdayBookAuthorship
  "A page attributed to Trump has been publicly reported; Trump denies writing or sending it and has sued the Wall Street Journal. The authorship claim remains disputed in this owner."
  false false false true

epsteinKnowledgeClaimReceipt : TrumpEpsteinReceipt
epsteinKnowledgeClaimReceipt = trump-epstein-receipt
  epsteinKnowledgeClaim
  "House-released Epstein emails include Epstein claiming Trump 'knew about the girls'. This is Epstein's claim, not an independently established fact; AP reports Giuffre consistently said Trump did not engage in misconduct toward her and did not know of Epstein's crimes."
  false true false true

uncorroboratedFBIAllegationReceipt : TrumpEpsteinReceipt
uncorroboratedFBIAllegationReceipt = trump-epstein-receipt
  uncorroboratedFBIAllegation
  "DOJ-released FBI interview records contain uncorroborated allegations against Trump; DOJ described them as unverified and Trump denies wrongdoing. Their existence is established, their truth is not."
  false true false true

recordsReleaseGovernanceReceipt : TrumpEpsteinReceipt
recordsReleaseGovernanceReceipt = trump-epstein-receipt
  recordsReleaseGovernance
  "2025-26 disputes over DOJ release, withholding, miscoding and later publication of Epstein records are a separate presidential/governance surface and do not alter the historical relationship facts by themselves."
  false true false true

------------------------------------------------------------------------
-- Cross-pollination with existing Trumpism interpretation machinery.
------------------------------------------------------------------------

trumpismContextAvailable : Bool
trumpismContextAvailable = true

trumpismContextDoesNotPayHistoricalEpsteinEdge : Bool
trumpismContextDoesNotPayHistoricalEpsteinEdge = false

------------------------------------------------------------------------
-- Canonical boundary.
------------------------------------------------------------------------

record TrumpEpsteinBoundary : Set where
  constructor trump-epstein-boundary
  field
    historicalSocialRelationshipEstablished : Bool
    repeatedEpsteinPlaneTravelEstablished : Bool
    marALagoRecruitmentLocusEstablished : Bool
    trumpStatedBanReasonRecorded : Bool
    criminalParticipationEstablished : Bool
    knowledgeOfEpsteinCrimesEstablished : Bool
    disputedAllegationPromotedToFact : Bool
    trumpismInterpretationPromotesRelationshipFact : Bool
open TrumpEpsteinBoundary public

canonicalTrumpEpsteinBoundary : TrumpEpsteinBoundary
canonicalTrumpEpsteinBoundary = trump-epstein-boundary
  true true true true false false false false

------------------------------------------------------------------------
-- Attribution / promotion firewalls.
------------------------------------------------------------------------

data SocialRelationshipImpliesCriminalParticipation : Set where
data FlightImpliesIslandVisit : Set where
data RecruitmentLocusImpliesOwnerKnowledge : Set where
data EpsteinClaimImpliesKnowledge : Set where
data FBIAllegationImpliesFact : Set where
data PoliticalInterpretationImpliesHistoricalEdge : Set where
data PresidentialRecordsHandlingChangesHistoricalTruth : Set where

socialRelationshipDoesNotCreateCriminalParticipation :
  SocialRelationshipImpliesCriminalParticipation → ⊥
socialRelationshipDoesNotCreateCriminalParticipation ()

flightDoesNotCreateIslandVisit : FlightImpliesIslandVisit → ⊥
flightDoesNotCreateIslandVisit ()

recruitmentLocusDoesNotCreateOwnerKnowledge : RecruitmentLocusImpliesOwnerKnowledge → ⊥
recruitmentLocusDoesNotCreateOwnerKnowledge ()

epsteinClaimDoesNotCreateKnowledge : EpsteinClaimImpliesKnowledge → ⊥
epsteinClaimDoesNotCreateKnowledge ()

uncorroboratedAllegationDoesNotCreateFact : FBIAllegationImpliesFact → ⊥
uncorroboratedAllegationDoesNotCreateFact ()

trumpismInterpretationDoesNotCreateHistoricalEdge :
  PoliticalInterpretationImpliesHistoricalEdge → ⊥
trumpismInterpretationDoesNotCreateHistoricalEdge ()

recordsHandlingDoesNotRewriteHistoricalTruth :
  PresidentialRecordsHandlingChangesHistoricalTruth → ⊥
recordsHandlingDoesNotRewriteHistoricalTruth ()
