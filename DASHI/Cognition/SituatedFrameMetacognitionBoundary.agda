module DASHI.Cognition.SituatedFrameMetacognitionBoundary where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Foundations.RepresentationChartInvariant as Representation

------------------------------------------------------------------------
-- 1.0 and 1.1 are role labels: first-order content versus content plus an
-- explicit account of the frame through which it is being read.
------------------------------------------------------------------------

data KnowledgeOrder : Set where
  firstOrderKnowledge : KnowledgeOrder
  frameAwareKnowledge : KnowledgeOrder
  comparativeFrameKnowledge : KnowledgeOrder

record SituatedState (Experience Frame : Set) : Set where
  constructor situated-state
  field
    experience : Experience
    activeFrame : Frame

record ComparativeSituatedState (Experience Frame : Set) : Set where
  field
    experience : Experience
    sourceFrame : Frame
    comparisonFrame : Frame
    transitionLabel : String

metacognitiveLift :
  ∀ {Experience Frame : Set} →
  Experience → Frame → SituatedState Experience Frame
metacognitiveLift x frame = situated-state x frame

metacognitiveLiftPreservesExperience :
  ∀ {Experience Frame : Set}
    (x : Experience)
    (frame : Frame) →
  SituatedState.experience (metacognitiveLift x frame) ≡ x
metacognitiveLiftPreservesExperience x frame = refl

------------------------------------------------------------------------
-- Distress is an experience; explanations are plural situated frames.
------------------------------------------------------------------------

data DistressExplanationFrame : Set where
  biologicalFrame : DistressExplanationFrame
  psychologicalFrame : DistressExplanationFrame
  interpersonalFrame : DistressExplanationFrame
  clinicalFrame : DistressExplanationFrame
  socialFrame : DistressExplanationFrame
  economicFrame : DistressExplanationFrame
  institutionalFrame : DistressExplanationFrame
  relationalFrame : DistressExplanationFrame
  selfAuthoredFrame : DistressExplanationFrame

data ExplanationScope : Set where
  partialScope : ExplanationScope
  overlappingScope : ExplanationScope
  contestedScope : ExplanationScope
  locallySupportedScope : ExplanationScope

record SituatedExplanation (Experience : Set) : Set where
  field
    observedExperience : Experience
    explanatoryFrame : DistressExplanationFrame
    scope : ExplanationScope
    evidenceLabel : String

record PluralFrameLedger (Experience : Set) : Set₁ where
  field
    explanations : List (SituatedExplanation Experience)
    noSingleFrameTotalized : Bool
    livedExperienceNotErased : Bool
    clinicalAuthorityClaimed : Bool
    structuralAuthorityClaimed : Bool

------------------------------------------------------------------------
-- Claim provenance separates source, synthesis, formal extension and future
-- empirical work.
------------------------------------------------------------------------

data ClaimLayer : Set where
  sourceClaim : ClaimLayer
  crossSourceInference : ClaimLayer
  dashiFormalExtension : ClaimLayer
  empiricalHypothesis : ClaimLayer
  interpretiveAnalogy : ClaimLayer

record LayeredClaim : Set where
  field
    statement : String
    layer : ClaimLayer
    sourceLabel : String
    authorityPromoted : Bool

------------------------------------------------------------------------
-- Philosophical precedents are recorded as interpretive neighbours, not as
-- proofs that a psychological or political reading is universally true.
------------------------------------------------------------------------

data InterpretivePrecedent : Set where
  standpointTheory : InterpretivePrecedent
  subjugatedKnowledges : InterpretivePrecedent
  patternMind : InterpretivePrecedent
  ideologyCritique : InterpretivePrecedent
  symptomReading : InterpretivePrecedent
  materialFeedbackIntervention : InterpretivePrecedent

record PrecedentRelation : Set where
  field
    precedent : InterpretivePrecedent
    relationLabel : String
    sourceAuthorLabel : String
    formalEquivalenceClaimed : Bool
    interpretiveUseOnly : Bool

canonicalPrecedentRelations : List PrecedentRelation
canonicalPrecedentRelations =
  record
    { precedent = standpointTheory
    ; relationLabel = "situated dual-perspective analogy"
    ; sourceAuthorLabel = "Georg Lukacs; Patricia Hill Collins and wider standpoint traditions"
    ; formalEquivalenceClaimed = false
    ; interpretiveUseOnly = true
    }
  ∷ record
    { precedent = subjugatedKnowledges
    ; relationLabel = "institutionally disqualified local knowledge remains inspectable"
    ; sourceAuthorLabel = "Michel Foucault"
    ; formalEquivalenceClaimed = false
    ; interpretiveUseOnly = true
    }
  ∷ record
    { precedent = patternMind
    ; relationLabel = "knowledge as relational and place-bound compression"
    ; sourceAuthorLabel = "Tyson Yunkaporta"
    ; formalEquivalenceClaimed = false
    ; interpretiveUseOnly = true
    }
  ∷ record
    { precedent = materialFeedbackIntervention
    ; relationLabel = "political intervention targets a material feedback loop rather than only its narrative surface"
    ; sourceAuthorLabel = "Marxian and materialist political traditions"
    ; formalEquivalenceClaimed = false
    ; interpretiveUseOnly = true
    }
  ∷ []

------------------------------------------------------------------------
-- Phase observations are contextual maps, never literal meanings of integers.
------------------------------------------------------------------------

record PhaseObservation (System : Set) : Set₁ where
  field
    Signature : Set
    InterpretationContext : Set
    Evidence : Set
    observationMap : System → Signature
    context : InterpretationContext
    evidence : Evidence

record MaterialFeedbackIntervention (System Action : Set) : Set₁ where
  field
    diagnoseFrame : System → String
    candidateAction : System → Action
    feedbackTarget : String
    interventionAuthorityClaimed : Bool
    outcomeGuaranteed : Bool

------------------------------------------------------------------------
-- Logistic-map roles are separated: x = 1/2 is a state-coordinate critical
-- point; r = 3 and the period-doubling accumulation value are parameter roles.
------------------------------------------------------------------------

data LogisticRole : Set where
  stateCriticalPointRole : LogisticRole
  firstPeriodDoublingParameterRole : LogisticRole
  accumulationParameterRole : LogisticRole
  periodThreeChaosCriterionRole : LogisticRole
  metaphoricalStageReadingRole : LogisticRole

record LogisticRoleReceipt : Set where
  field
    role : LogisticRole
    valueLabel : String
    mathematicalRoleLabel : String
    identifiedWithUniversalDecisionBoundary : Bool

logisticHalfReceipt : LogisticRoleReceipt
logisticHalfReceipt = record
  { role = stateCriticalPointRole
  ; valueLabel = "x = 1/2"
  ; mathematicalRoleLabel = "critical point of x -> r*x*(1-x) as a function of x"
  ; identifiedWithUniversalDecisionBoundary = false
  }

logisticFirstDoublingReceipt : LogisticRoleReceipt
logisticFirstDoublingReceipt = record
  { role = firstPeriodDoublingParameterRole
  ; valueLabel = "r = 3"
  ; mathematicalRoleLabel = "first period-doubling threshold in the standard logistic family"
  ; identifiedWithUniversalDecisionBoundary = false
  }

logisticAccumulationReceipt : LogisticRoleReceipt
logisticAccumulationReceipt = record
  { role = accumulationParameterRole
  ; valueLabel = "r approximately 3.5699456"
  ; mathematicalRoleLabel = "period-doubling accumulation parameter"
  ; identifiedWithUniversalDecisionBoundary = false
  }

------------------------------------------------------------------------
-- Primorial transforms are arithmetic operators.  Interpretive readings are
-- downstream and require their own evidence.
------------------------------------------------------------------------

data PrimorialTransformRole : Set where
  primorialBaseExpFunctionRole : PrimorialTransformRole
  secondIterateRole : PrimorialTransformRole
  primeExponentVectorRole : PrimorialTransformRole
  optionalInterpretiveProjectionRole : PrimorialTransformRole

record PrimorialTransformBoundary : Set where
  field
    a276086Role : PrimorialTransformRole
    a276087Role : PrimorialTransformRole
    secondIsIterateOfFirst : Bool
    systemicRebirthProvedBySequence : Bool
    logisticBranchesEncodedWithoutAdapter : Bool
    interpretationRequiresSeparateMap : Bool

canonicalPrimorialTransformBoundary : PrimorialTransformBoundary
canonicalPrimorialTransformBoundary = record
  { a276086Role = primorialBaseExpFunctionRole
  ; a276087Role = secondIterateRole
  ; secondIsIterateOfFirst = true
  ; systemicRebirthProvedBySequence = false
  ; logisticBranchesEncodedWithoutAdapter = false
  ; interpretationRequiresSeparateMap = true
  }

------------------------------------------------------------------------
-- Mental-health and political non-promotion boundary.
------------------------------------------------------------------------

record SituatedFrameAuthorityBoundary : Set where
  field
    distressProvesSystemIncoherence : Bool
    distressIsOnlyBiologicalDefect : Bool
    subjectEscapesAllFrames : Bool
    frameMayBeInspected : Bool
    multipleCausesMayOverlap : Bool
    diagnosisAuthorityClaimed : Bool
    treatmentAuthorityClaimed : Bool
    politicalOutcomeGuaranteed : Bool

canonicalSituatedFrameAuthorityBoundary : SituatedFrameAuthorityBoundary
canonicalSituatedFrameAuthorityBoundary = record
  { distressProvesSystemIncoherence = false
  ; distressIsOnlyBiologicalDefect = false
  ; subjectEscapesAllFrames = false
  ; frameMayBeInspected = true
  ; multipleCausesMayOverlap = true
  ; diagnosisAuthorityClaimed = false
  ; treatmentAuthorityClaimed = false
  ; politicalOutcomeGuaranteed = false
  }

frameAwareSummary : String
frameAwareSummary =
  "The 1.1 move preserves experience while exposing the active explanatory chart for comparison; it does not grant a view from nowhere, a diagnosis, or a guaranteed political conclusion."
