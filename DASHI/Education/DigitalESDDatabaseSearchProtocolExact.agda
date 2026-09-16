module DASHI.Education.DigitalESDDatabaseSearchProtocolExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDStructuredSearchExact as Search

------------------------------------------------------------------------
-- VERSIONED PLATFORM-NEUTRAL SEARCH PROTOCOL
--
-- The search concepts are frozen here before database execution. This is not a
-- substitute for platform-specific syntax, controlled vocabulary, field codes,
-- proximity operators or actual execution. Every translated query must be
-- retained verbatim inside the future DatabaseExecutionReceipt.
------------------------------------------------------------------------

protocolVersion : String
protocolVersion = "digital-esd-search-v1-2026-09-16"

record ConceptBlock : Set where
  constructor concept-block
  field
    blockLabel : String
    expression : String
    scopeNote : String

open ConceptBlock public

digitalEducationBlock : ConceptBlock
digitalEducationBlock = concept-block
  "A: digital education / educational technology"
  "(\"digital education\" OR \"digital learning\" OR \"educational technology\" OR edtech OR \"online learning\" OR \"blended learning\" OR \"digital learning platform*\" OR \"generative AI\" OR GenAI OR \"artificial intelligence\")"
  "Broad digital-education carrier; platform translations may add controlled vocabulary but may not silently drop the retained concepts."

esdBlock : ConceptBlock
esdBlock = concept-block
  "B: education for sustainable development / sustainability"
  "(\"education for sustainable development\" OR ESD OR \"sustainable development education\" OR \"sustainability education\" OR \"environmental education\" OR \"sustainable education\")"
  "ESD/sustainability education carrier; environmental education remains a related but not definitionally identical source family."

transformationBlock : ConceptBlock
transformationBlock = concept-block
  "C: educational transformation / institutional change"
  "(transform* OR \"system change\" OR institutional* OR \"institutional change\" OR \"whole institution\" OR curriculum OR pedagogy OR competenc* OR \"learning environment*\")"
  "Distinguishes technology adoption from pedagogical/institutional/system transformation questions."

reflexiveSustainabilityBlock : ConceptBlock
reflexiveSustainabilityBlock = concept-block
  "D: sustainability of digital technology / lifecycle / circularity"
  "(\"life cycle assessment\" OR LCA OR energy OR electricity OR carbon OR emission* OR water OR \"e-waste\" OR circular* OR repair* OR reuse OR recycl* OR upgrade* OR durability OR \"service life\")"
  "Reverse-direction sustainability carrier; does not presume that all retrieved records provide a complete lifecycle assessment."

participantGovernanceBlock : ConceptBlock
participantGovernanceBlock = concept-block
  "E: participant agency / voice / governance"
  "(\"student voice\" OR \"learner voice\" OR \"learner agency\" OR \"student agency\" OR participatory OR \"participatory research\" OR co-design OR codesign OR governance OR \"public accountability\")"
  "Participation/governance carrier; retrieval does not promote consultation or consent into constitutive epistemic authority."

longitudinalDurabilityBlock : ConceptBlock
longitudinalDurabilityBlock = concept-block
  "F: longitudinal / durability / institutionalisation"
  "(longitudinal OR long-term OR durability OR sustainab* OR institutionalisation OR institutionalization OR persistence OR retention OR follow-up OR \"follow up\")"
  "Time/durability carrier; sustainability terms require consumer-relative interpretation to avoid semantic flattening."

openInfrastructureBlock : ConceptBlock
openInfrastructureBlock = concept-block
  "G: open/interoperable/repairable infrastructure"
  "(interoperab* OR \"open standard*\" OR \"open source\" OR OER OR \"open educational resource*\" OR portability OR migration OR export* OR \"vendor lock-in\" OR repairab* OR \"right to repair\")"
  "Infrastructure/governance carrier; normative openness does not prove deployed persistence or repairability."

record PlannedQuery : Set where
  constructor planned-query
  field
    queryId : String
    family : Search.SearchQueryFamily
    researchPurpose : String
    platformNeutralExpression : String
    protocolVersionRetained : String
    translatedDatabaseSyntaxObserved : Bool
    translatedDatabaseSyntaxObservedIsFalse :
      translatedDatabaseSyntaxObserved ≡ false
    databaseExecutionObserved : Bool
    databaseExecutionObservedIsFalse : databaseExecutionObserved ≡ false

open PlannedQuery public

q1DigitalEducationESD : PlannedQuery
q1DigitalEducationESD = planned-query
  "Q1-digital-education-esd"
  Search.digitalEducationESD
  "identify literature on digital education/technology used in or for ESD and sustainability education"
  "A AND B"
  protocolVersion
  false refl
  false refl

q2Transformation : PlannedQuery
q2Transformation = planned-query
  "Q2-transformation-beyond-adoption"
  Search.digitalEducationESD
  "identify conditions linking digital education and ESD to pedagogical, curricular, institutional or system transformation"
  "A AND B AND C"
  protocolVersion
  false refl
  false refl

q3ReflexiveSustainability : PlannedQuery
q3ReflexiveSustainability = planned-query
  "Q3-sustainability-of-digital-education"
  Search.reflexiveDigitalSustainability
  "identify environmental/material/lifecycle consequences and sustainability constraints on digital education itself"
  "A AND D"
  protocolVersion
  false refl
  false refl

q4ParticipantGovernance : PlannedQuery
q4ParticipantGovernance = planned-query
  "Q4-participant-agency-governance"
  Search.participantAgencyGovernance
  "identify participant agency, student voice, co-design and governance evidence in digital education and/or ESD"
  "A AND B AND E"
  protocolVersion
  false refl
  false refl

q5LongitudinalInstitutional : PlannedQuery
q5LongitudinalInstitutional = planned-query
  "Q5-longitudinal-institutional"
  Search.longitudinalInstitutionalImpact
  "identify longitudinal, persistent and institutionalised effects or conditions in digital-ESD and adjacent ESD/digital-education evidence"
  "A AND B AND F"
  protocolVersion
  false refl
  false refl

q6OpenInteroperableRepairable : PlannedQuery
q6OpenInteroperableRepairable = planned-query
  "Q6-open-interoperable-repairable"
  Search.openInteroperabilityRepairability
  "identify openness, interoperability, portability, vendor-lock-in, repairability and related durability evidence for digital learning infrastructure"
  "A AND G"
  protocolVersion
  false refl
  false refl

canonicalPlannedQueries : List PlannedQuery
canonicalPlannedQueries =
  q1DigitalEducationESD
  ∷ q2Transformation
  ∷ q3ReflexiveSustainability
  ∷ q4ParticipantGovernance
  ∷ q5LongitudinalInstitutional
  ∷ q6OpenInteroperableRepairable
  ∷ []

plannedQueryCount : Nat
plannedQueryCount = 6

------------------------------------------------------------------------
-- Declared database translation surfaces.
------------------------------------------------------------------------

record DatabaseTranslationPlan : Set where
  constructor database-translation-plan
  field
    surface : Search.SearchSurface
    protocolReference : String
    exactTranslatedQueriesObserved : Bool
    exactTranslatedQueriesObservedIsFalse :
      exactTranslatedQueriesObserved ≡ false
    executionReceiptObserved : Bool
    executionReceiptObservedIsFalse : executionReceiptObserved ≡ false

open DatabaseTranslationPlan public

scopusPlan : DatabaseTranslationPlan
scopusPlan = database-translation-plan Search.scopus protocolVersion false refl false refl

webOfSciencePlan : DatabaseTranslationPlan
webOfSciencePlan = database-translation-plan Search.webOfScience protocolVersion false refl false refl

ericPlan : DatabaseTranslationPlan
ericPlan = database-translation-plan Search.eric protocolVersion false refl false refl

acmPlan : DatabaseTranslationPlan
acmPlan = database-translation-plan Search.acmDigitalLibrary protocolVersion false refl false refl

ieeePlan : DatabaseTranslationPlan
ieeePlan = database-translation-plan Search.ieeeXplore protocolVersion false refl false refl

canonicalDatabaseTranslationPlans : List DatabaseTranslationPlan
canonicalDatabaseTranslationPlans =
  scopusPlan ∷ webOfSciencePlan ∷ ericPlan ∷ acmPlan ∷ ieeePlan ∷ []

------------------------------------------------------------------------
-- Execution / promotion firewalls.
------------------------------------------------------------------------

data PlannedQueryCreatesExecutionReceipt : Set where
data PlatformNeutralQueryEqualsDatabaseSpecificSyntax : Set where
data QueryPlanCreatesSearchCompleteness : Set where
data SearchTermPresenceDeterminesEligibility : Set where

plannedQueryDoesNotCreateExecutionReceipt : PlannedQueryCreatesExecutionReceipt → ⊥
plannedQueryDoesNotCreateExecutionReceipt ()

platformNeutralQueryDoesNotEqualDatabaseSpecificSyntax :
  PlatformNeutralQueryEqualsDatabaseSpecificSyntax → ⊥
platformNeutralQueryDoesNotEqualDatabaseSpecificSyntax ()

queryPlanDoesNotCreateSearchCompleteness : QueryPlanCreatesSearchCompleteness → ⊥
queryPlanDoesNotCreateSearchCompleteness ()

searchTermPresenceDoesNotDetermineEligibility :
  SearchTermPresenceDeterminesEligibility → ⊥
searchTermPresenceDoesNotDetermineEligibility ()

record SearchProtocolBoundary : Set where
  constructor search-protocol-boundary
  field
    protocolVersionFrozenBeforeExecution : Bool
    protocolVersionFrozenBeforeExecutionIsTrue :
      protocolVersionFrozenBeforeExecution ≡ true
    allSixQueryFamiliesRetained : Bool
    allSixQueryFamiliesRetainedIsTrue : allSixQueryFamiliesRetained ≡ true
    platformSpecificTranslationStillRequired : Bool
    platformSpecificTranslationStillRequiredIsTrue :
      platformSpecificTranslationStillRequired ≡ true
    exactQueryMustBeRetainedAtExecution : Bool
    exactQueryMustBeRetainedAtExecutionIsTrue :
      exactQueryMustBeRetainedAtExecution ≡ true
    databaseExecutionObserved : Bool
    databaseExecutionObservedIsFalse : databaseExecutionObserved ≡ false
    queryPlanEqualsExecutionReceipt : Bool
    queryPlanEqualsExecutionReceiptIsFalse :
      queryPlanEqualsExecutionReceipt ≡ false
    queryPlanEqualsEvidenceCompleteness : Bool
    queryPlanEqualsEvidenceCompletenessIsFalse :
      queryPlanEqualsEvidenceCompleteness ≡ false

open SearchProtocolBoundary public

canonicalSearchProtocolBoundary : SearchProtocolBoundary
canonicalSearchProtocolBoundary =
  search-protocol-boundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
