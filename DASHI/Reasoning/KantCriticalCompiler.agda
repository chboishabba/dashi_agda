module DASHI.Reasoning.KantCriticalCompiler where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Source calibration: Immanuel Kant, Critique of Pure Reason,
-- DOI 10.1017/CBO9780511804649; Critique of the Power of Judgment,
-- DOI 10.1017/CBO9780511804656.
--
-- Kant as a critical compiler: categories require schemata, reflective
-- judgment produces candidates, and regulative ideas do not silently become
-- constitutive objects.
------------------------------------------------------------------------

data KantCategory : Set where
  unity plurality totality : KantCategory
  reality negation limitation : KantCategory
  substance causality community : KantCategory
  possibility existence necessity : KantCategory

data JudgmentMode : Set where
  determiningJudgment reflectiveJudgment : JudgmentMode

data IdeaUse : Set where
  regulativeUse constitutiveUse : IdeaUse

data CriticalBoundary : Set where
  thingInItselfBoundary : CriticalBoundary
  worldTotalityBoundary : CriticalBoundary
  subjectSubstanceBoundary : CriticalBoundary
  necessaryBeingBoundary : CriticalBoundary

data TranscendentalIllusion : Set where
  subjectUnityReifiedAsSoul : TranscendentalIllusion
  experientialSeriesReifiedAsWorldWhole : TranscendentalIllusion
  systematicUnityReifiedAsNecessaryBeing : TranscendentalIllusion

data CriticalResult : Set where
  constitutiveResult : CriticalResult
  regulativeResult : CriticalResult
  contradictionResult : CriticalResult
  antinomicResult : CriticalResult
  noTypedMeetResult : CriticalResult
  scopeExceededResult : CriticalResult
  formallyValidEquivocationResult : CriticalResult
  transcendentalIllusionResult : CriticalResult

record CategorySchema
  (Observation Context : Set)
  (category : KantCategory) : Set₁ where
  field
    appliesInContext : Observation → Context → Set
    temporalRule : Observation → Context → Set
    scopeReceipt : String

record ConstitutiveJudgment
  (Observation Context Object : Set)
  (category : KantCategory) : Set₁ where
  field
    observation : Observation
    context : Context
    schema : CategorySchema Observation Context category
    synthesise : Observation → Context → Object
    result : Object
    resultMatchesSynthesis : result ≡ synthesise observation context
    evidenceReceipt : String
    scopeReceipt : String

record ReflectiveJudgmentResult (Observation : Set) : Set₁ where
  field
    observations : List Observation
    candidateUniversals : List String
    searchReceipt : String
    promotionClaimed : Bool
    promotionClaimedIsFalse : promotionClaimed ≡ false
    furtherVerificationRequired : Bool
    furtherVerificationRequiredIsTrue :
      furtherVerificationRequired ≡ true

record RegulativeIdea : Set where
  field
    searchDirection : String
    desiredSystematicUnity : String
    candidateGenerator : String
    objectExistenceClaimed : Bool
    objectExistenceClaimedIsFalse :
      objectExistenceClaimed ≡ false

canonicalRegulativeIdea : RegulativeIdea
canonicalRegulativeIdea = record
  { searchDirection = "seek systematic unity among certified judgments"
  ; desiredSystematicUnity = "regulative horizon, not a constituted object"
  ; candidateGenerator = "reflective candidate generation"
  ; objectExistenceClaimed = false
  ; objectExistenceClaimedIsFalse = refl
  }

record ParalogismReceipt : Set where
  field
    inferenceLabel : String
    logicalSubjectUse : String
    substantialObjectUse : String
    formalShapeAdmissible : Bool
    middleTermReferenceShift : Bool
    result : CriticalResult
    objectAuthorityPromoted : Bool
    objectAuthorityPromotedIsFalse :
      objectAuthorityPromoted ≡ false

canonicalSubjectParalogismReceipt : ParalogismReceipt
canonicalSubjectParalogismReceipt = record
  { inferenceLabel = "unity of apperception to substantial soul"
  ; logicalSubjectUse = "I as synthesis index of representations"
  ; substantialObjectUse = "I as persistent object-substance"
  ; formalShapeAdmissible = true
  ; middleTermReferenceShift = true
  ; result = formallyValidEquivocationResult
  ; objectAuthorityPromoted = false
  ; objectAuthorityPromotedIsFalse = refl
  }

record KantCriticalCompilerBoundary : Set where
  field
    categoryWithoutSchemaProducesJudgment : Bool
    reflectiveJudgmentDirectlyPromotes : Bool
    regulativeIdeaConstitutesObject : Bool
    phenomenonEqualsUnknownNoumenon : Bool
    apperceptionImpliesSubstantialSoul : Bool
    paralogismDistinctFromNoTypedMeet : Bool
    paralogismDistinctFromAntinomy : Bool
    criticalBoundaryIsRepresentedObject : Bool
    boundaryNote : String

canonicalKantCriticalCompilerBoundary : KantCriticalCompilerBoundary
canonicalKantCriticalCompilerBoundary = record
  { categoryWithoutSchemaProducesJudgment = false
  ; reflectiveJudgmentDirectlyPromotes = false
  ; regulativeIdeaConstitutesObject = false
  ; phenomenonEqualsUnknownNoumenon = false
  ; apperceptionImpliesSubstantialSoul = false
  ; paralogismDistinctFromNoTypedMeet = true
  ; paralogismDistinctFromAntinomy = true
  ; criticalBoundaryIsRepresentedObject = false
  ; boundaryNote =
      "Kantian critique is a scope and synthesis discipline: categories need schemata, reflection proposes, and transcendental boundaries block object-level promotion."
  }
