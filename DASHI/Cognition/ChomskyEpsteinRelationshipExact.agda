module DASHI.Cognition.ChomskyEpsteinRelationshipExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- CHOMSKY <-> EPSTEIN RELATIONSHIP OWNER
--
-- This owner is deliberately separate from the Bach 2016 proposed-invite list
-- in ChomskyLanguageAIDisputeExact.  A proposed invite does not prove a
-- relationship; independently released 2025-26 correspondence does.
------------------------------------------------------------------------

data RelationshipEdgeKind : Set where
  regularContact : RelationshipEdgeKind
  socialMeeting : RelationshipEdgeKind
  financialAdvice : RelationshipEdgeKind
  introductionBrokerage : RelationshipEdgeKind
  projectAdministrationPayment : RelationshipEdgeKind
  travelInvitation : RelationshipEdgeKind

record ChomskyEpsteinRelationshipReceipt : Set where
  constructor chomsky-epstein-relationship-receipt
  field
    edgeKind : RelationshipEdgeKind
    sourceDescription : String
    directOrContemporaneousRecord : Bool
    relationshipEstablished : Bool
    criminalParticipationEstablished : Bool
    scientificEndorsementEstablished : Bool
open ChomskyEpsteinRelationshipReceipt public

regularContactReceipt : ChomskyEpsteinRelationshipReceipt
regularContactReceipt = chomsky-epstein-relationship-receipt
  regularContact
  "2025 House/DOJ-released correspondence: Chomsky described regular contact with Epstein as a most valuable experience; later 2026 releases add repeated direct correspondence."
  true true false false

socialMeetingReceipt : ChomskyEpsteinRelationshipReceipt
socialMeetingReceipt = chomsky-epstein-relationship-receipt
  socialMeeting
  "2016 correspondence records repeated social meetings/dinner planning and invitations involving New York and the Caribbean."
  true true false false

financialAdviceReceipt : ChomskyEpsteinRelationshipReceipt
financialAdviceReceipt = chomsky-epstein-relationship-receipt
  financialAdvice
  "Released correspondence shows Chomsky seeking Epstein's advice during a financial/estate dispute involving an apartment and a USD 187,000 payment."
  true true false false

bannonIntroductionReceipt : ChomskyEpsteinRelationshipReceipt
bannonIntroductionReceipt = chomsky-epstein-relationship-receipt
  introductionBrokerage
  "Released correspondence shows Chomsky contacting Steve Bannon using contact information supplied by Epstein and seeking a meeting."
  true true false false

chomskyChallengePaymentReceipt : ChomskyEpsteinRelationshipReceipt
chomskyChallengePaymentReceipt = chomsky-epstein-relationship-receipt
  projectAdministrationPayment
  "Released correspondence reports a USD 20,000 cheque sent through an Epstein associate to help administer the 'Chomsky challenge in linguistics'."
  true true false false

caribbeanInvitationReceipt : ChomskyEpsteinRelationshipReceipt
caribbeanInvitationReceipt = chomsky-epstein-relationship-receipt
  travelInvitation
  "Released 2016 correspondence records Epstein inviting the Chomskys to New York or the Caribbean and Chomsky expressing enthusiasm about the Caribbean."
  true true false false

------------------------------------------------------------------------
-- PROMOTION FIREWALLS
------------------------------------------------------------------------

data RelationshipImpliesCriminalParticipation : Set where
data RelationshipValidatesScientificJudgment : Set where
data FinancialAdviceImpliesResearchFunding : Set where
data ProjectPaymentImpliesEpsteinAuthorship : Set where

data ContactImpliesKnowledgeOfAllCrimes : Set where

relationshipDoesNotImplyCriminalParticipation :
  RelationshipImpliesCriminalParticipation → ⊥
relationshipDoesNotImplyCriminalParticipation ()

relationshipDoesNotValidateEpsteinScientificJudgment :
  RelationshipValidatesScientificJudgment → ⊥
relationshipDoesNotValidateEpsteinScientificJudgment ()

financialAdviceDoesNotEqualResearchFunding :
  FinancialAdviceImpliesResearchFunding → ⊥
financialAdviceDoesNotEqualResearchFunding ()

projectPaymentDoesNotEstablishEpsteinAuthorship :
  ProjectPaymentImpliesEpsteinAuthorship → ⊥
projectPaymentDoesNotEstablishEpsteinAuthorship ()

contactDoesNotEstablishKnowledgeOfAllCrimes :
  ContactImpliesKnowledgeOfAllCrimes → ⊥
contactDoesNotEstablishKnowledgeOfAllCrimes ()

record ChomskyEpsteinRelationshipBoundary : Set where
  constructor chomsky-epstein-relationship-boundary
  field
    directRelationshipEstablished : Bool
    repeatedContactEstablished : Bool
    socialContactEstablished : Bool
    brokerageEstablished : Bool
    criminalParticipationEstablished : Bool
    scientificControlEstablished : Bool

canonicalChomskyEpsteinRelationshipBoundary : ChomskyEpsteinRelationshipBoundary
canonicalChomskyEpsteinRelationshipBoundary =
  chomsky-epstein-relationship-boundary true true true true false false
