module DASHI.Education.DigitalESDDatabaseSearchProtocolV2Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Education.DigitalESDDatabaseSearchProtocolExact as V1
import DASHI.Education.DigitalESDDisabilityIntersectionalityAuditExact as Disability
import DASHI.Education.DigitalESDStudyIntersectionalAbsenceAuditExact as Absence

------------------------------------------------------------------------
-- VERSIONED DIGITAL-ESD SEARCH PROTOCOL AMENDMENT V2
--
-- v1 remains frozen history.  This owner adds political-economy, social-
-- provisioning and maintenance/durability concept blocks before the next
-- successful database execution.  It does not rewrite or backdate v1.
------------------------------------------------------------------------

protocolVersion : String
protocolVersion = "digital-esd-search-v2-2026-09-17"

parentProtocolVersion : String
parentProtocolVersion = V1.protocolVersion

record AmendmentConceptBlock : Set where
  constructor amendment-concept-block
  field
    blockLabel : String
    expression : String
    scopeNote : String

open AmendmentConceptBlock public

politicalEconomyBlock : AmendmentConceptBlock
politicalEconomyBlock = amendment-concept-block
  "H: political economy / ownership / incentives"
  "(capitalis* OR \"political economy\" OR ownership OR privati* OR public OR nonprofit OR non-profit OR cooperative OR commons OR competition OR market* OR monopoly OR oligopoly OR profit OR revenue OR financing OR subsidy OR procurement OR licensing OR \"intellectual property\" OR \"vendor lock-in\" OR externalit* OR labour OR labor)"
  "Mechanism-discriminating carrier. Retrieval of a political-economy label does not establish structural causation or waste."

socialProvisioningBlock : AmendmentConceptBlock
socialProvisioningBlock = amendment-concept-block
  "I: social provisioning / school-linked services / community"
  "(\"school meal*\" OR breakfast OR lunch OR \"food security\" OR \"community school*\" OR \"integrated student support*\" OR counselling OR counseling OR \"health service*\" OR supervision OR care OR \"community connection\" OR \"social connection\" OR extracurricular OR \"third space\" OR \"third place\")"
  "Retrieves non-instructional provisioning potentially lost, shifted or recreated by delivery-mode change; no term implies a universal school function."

maintenanceDurabilityBlock : AmendmentConceptBlock
maintenanceDurabilityBlock = amendment-concept-block
  "J: maintenance / recurrent funding / institutional durability"
  "(maintenance OR maintain* OR stewardship OR recurrent OR recurring OR budget* OR funding OR defund* OR staffing OR turnover OR succession OR handover OR documentation OR \"professional learning\" OR \"professional development\" OR update* OR security OR migration OR portability OR decommission* OR resilience OR institutionalisation OR institutionalization)"
  "Durability carrier covering recurrent labour/resources, succession, governance and exit; launch/adoption remains distinct from sustained institutional capacity."

amendmentBlocks : List AmendmentConceptBlock
amendmentBlocks = politicalEconomyBlock ∷ socialProvisioningBlock ∷ maintenanceDurabilityBlock ∷ []

amendmentBlockCount : Nat
amendmentBlockCount = 3

record VersionedAmendmentQuery : Set where
  constructor versioned-amendment-query
  field
    queryId : String
    researchPurpose : String
    expression : String
    parentVersion : String
    amendmentVersion : String
    databaseSpecificTranslationRequired : Bool

open VersionedAmendmentQuery public

q8PoliticalEconomy : VersionedAmendmentQuery
q8PoliticalEconomy = versioned-amendment-query
  "Q8-political-economy-provisioning"
  "identify political-economic arrangements and mechanisms shaping digital-ESD ownership, incentives, duplication, externality allocation, procurement, labour, maintenance and exit"
  "(A OR B) AND H"
  parentProtocolVersion protocolVersion true

q9SocialProvisioning : VersionedAmendmentQuery
q9SocialProvisioning = versioned-amendment-query
  "Q9-social-provisioning-continuity"
  "identify school-linked food, care, community, health/social-service and accessibility provision that can be lost, shifted or recreated when educational delivery changes"
  "(A OR B) AND I"
  parentProtocolVersion protocolVersion true

q10MaintenanceDurability : VersionedAmendmentQuery
q10MaintenanceDurability = versioned-amendment-query
  "Q10-maintenance-institutional-durability"
  "identify recurrent funding, staffing, maintenance, succession, governance, migration and durability evidence for digital-education and ESD programmes"
  "(A OR B) AND J"
  parentProtocolVersion protocolVersion true

amendmentQueries : List VersionedAmendmentQuery
amendmentQueries = q8PoliticalEconomy ∷ q9SocialProvisioning ∷ q10MaintenanceDurability ∷ []

record V2IntersectionalExtractionChallenge : Set where
  constructor v2-intersectional-extraction-challenge
  field
    disabilityBoundary : Disability.DisabilityDigitalESDBoundary
    absenceQuestionCount : Nat
    everyNewExtractionFamilyReceivesChallenge : Bool
    everyNewExtractionFamilyReceivesChallengeIsTrue : everyNewExtractionFamilyReceivesChallenge ≡ true
    challengeReading : String

open V2IntersectionalExtractionChallenge public

canonicalV2IntersectionalExtractionChallenge : V2IntersectionalExtractionChallenge
canonicalV2IntersectionalExtractionChallenge = v2-intersectional-extraction-challenge
  Disability.canonicalDisabilityDigitalESDBoundary
  Absence.absenceAuditQuestionCount
  true refl
  "Political-economy, social-provisioning and durability records must each be challenged against the existing disability-specific and 'who is not at the table?' surfaces; broad equity or aggregate participation cannot substitute for that audit."

record SearchProtocolV2Boundary : Set where
  constructor search-protocol-v2-boundary
  field
    v1HistoryRetained : Bool
    v1HistoryRetainedIsTrue : v1HistoryRetained ≡ true
    newConceptsBackdatedIntoV1 : Bool
    newConceptsBackdatedIntoV1IsFalse : newConceptsBackdatedIntoV1 ≡ false
    exactDatabaseTranslationStillRequired : Bool
    exactDatabaseTranslationStillRequiredIsTrue : exactDatabaseTranslationStillRequired ≡ true
    executionReceiptCreatedByAmendment : Bool
    executionReceiptCreatedByAmendmentIsFalse : executionReceiptCreatedByAmendment ≡ false
    intersectionalChallengeMandatory : Bool
    intersectionalChallengeMandatoryIsTrue : intersectionalChallengeMandatory ≡ true

open SearchProtocolV2Boundary public

canonicalSearchProtocolV2Boundary : SearchProtocolV2Boundary
canonicalSearchProtocolV2Boundary = search-protocol-v2-boundary
  true refl
  false refl
  true refl
  false refl
  true refl
