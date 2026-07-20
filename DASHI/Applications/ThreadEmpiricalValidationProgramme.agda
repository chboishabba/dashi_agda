module DASHI.Applications.ThreadEmpiricalValidationProgramme where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Evidence programme shared by mental-health, cultural teaching, political
-- intervention, relational-process, and other thread applications.

record SourceReceipt : Set where
  constructor sourceReceipt
  field
    citation : String
    sourceType : String
    year : Nat
    accessibleForAudit : Bool
    interpretation : String

record PopulationContext : Set where
  constructor populationContext
  field
    population : String
    place : String
    timeWindow : String
    inclusionRule : String
    exclusionRule : String

record CompetingExplanation : Set where
  constructor competingExplanation
  field
    label : String
    mechanism : String
    supportingEvidence : List SourceReceipt
    disconfirmingObservation : String

record ConsentAuthorityReceipt : Set where
  constructor consentAuthorityReceipt
  field
    authorityHolder : String
    consentScope : String
    consentRecorded : Bool
    revocable : Bool
    communityAuthorityClaimed : Bool

record InterventionOutcome : Set where
  constructor interventionOutcome
  field
    intervention : String
    targetMechanism : String
    preMeasure : String
    postMeasure : String
    adverseEffects : List String
    rollbackUsed : Bool
    causalIdentificationMethod : String

record IndependentReviewReceipt : Set where
  constructor independentReviewReceipt
  field
    reviewer : String
    independenceBasis : String
    methodsReviewed : Bool
    dataReviewed : Bool
    conclusionsSupported : Bool
    limitations : String

record EmpiricalApplicationPackage : Set where
  constructor empiricalApplicationPackage
  field
    applicationName : String
    sources : List SourceReceipt
    context : PopulationContext
    competingExplanations : List CompetingExplanation
    disconfirmationCriteria : List String
    consentAndAuthority : ConsentAuthorityReceipt
    outcomes : List InterventionOutcome
    independentReviews : List IndependentReviewReceipt
    generalisationLimits : List String
    diagnosticAuthority : Bool
    politicalCausalAuthority : Bool
    culturalRepresentationAuthority : Bool

------------------------------------------------------------------------
-- One bounded, deliberately non-promoted scaffold.

placeholderSource : SourceReceipt
placeholderSource =
  sourceReceipt
    "user-supplied thread account; external source not yet vendored"
    "unverified application seed"
    2026
    false
    "retained as provenance-bearing input, not promoted evidence"

placeholderContext : PopulationContext
placeholderContext =
  populationContext
    "not yet selected"
    "not yet selected"
    "not yet selected"
    "requires preregistration"
    "requires preregistration"

placeholderConsent : ConsentAuthorityReceipt
placeholderConsent =
  consentAuthorityReceipt
    "not yet supplied"
    "no reuse beyond formal scaffold"
    false
    true
    false

canonicalUnvalidatedApplication : EmpiricalApplicationPackage
canonicalUnvalidatedApplication =
  empiricalApplicationPackage
    "thread application awaiting evidence"
    (placeholderSource ∷ [])
    placeholderContext
    []
    ("state at least one observation that would count against the preferred explanation" ∷ [])
    placeholderConsent
    []
    []
    ("no population-level or cross-cultural generalisation" ∷ [])
    false
    false
    false

record EmpiricalPromotionAuthority
    (application : EmpiricalApplicationPackage)
    : Set₁ where
  field
    sourceSufficiency : Set
    populationAndContextAdequate : Set
    competingExplanationsCompared : Set
    disconfirmationTested : Set
    consentAndAuthorityValid : Set
    outcomeMeasurementsComplete : Set
    adverseEffectsAudited : Set
    rollbackAudited : Set
    independentReviewComplete : Set
    claimedGeneralisationWithinLimits : Set

record ThreadEmpiricalValidationBoundary : Set where
  constructor threadEmpiricalValidationBoundary
  field
    applicationSchemaComplete : Bool
    placeholderCarriesPromotionAuthority : Bool
    placeholderCarriesPromotionAuthorityIsFalse :
      placeholderCarriesPromotionAuthority ≡ false
    distressAutomaticallySelectsSystemicCause : Bool
    distressAutomaticallySelectsSystemicCauseIsFalse :
      distressAutomaticallySelectsSystemicCause ≡ false
    frameAwarenessAutomaticallyDiagnoses : Bool
    frameAwarenessAutomaticallyDiagnosesIsFalse :
      frameAwarenessAutomaticallyDiagnoses ≡ false
    postInterventionChangeProvesUniqueMechanism : Bool
    postInterventionChangeProvesUniqueMechanismIsFalse :
      postInterventionChangeProvesUniqueMechanism ≡ false
    culturalAnalogyImpliesAuthority : Bool
    culturalAnalogyImpliesAuthorityIsFalse :
      culturalAnalogyImpliesAuthority ≡ false
    interpretation : String

canonicalThreadEmpiricalValidationBoundary :
  ThreadEmpiricalValidationBoundary
canonicalThreadEmpiricalValidationBoundary =
  threadEmpiricalValidationBoundary
    true
    false refl
    false refl
    false refl
    false refl
    false refl
    "the application schema names datasets, populations, rival explanations, falsifiers, consent, outcomes, harms, rollback and independent review; no application is promoted until a proof-carrying evidence package inhabits every required field"
