module DASHI.Biology.PedagogicalJPlusOneRouting where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Biology.OEFMultiFibreFeedbackHyperfabric as OEF

------------------------------------------------------------------------
-- Human-reviewed pedagogical +1 routing.
--
-- Model outputs route attention to residual hypotheses.  They do not issue
-- automatic interventions.  A +1 becomes admissible only through student
-- choice, contextual fit, low burden, non-shaming, non-surveillance,
-- human interpretation, and measurable evidence return.

data Never : Set where

data PromotionLevel : Set where
  rawFeedbackSurfaceLevel : PromotionLevel
  humanCodedOEFCandidateLevel : PromotionLevel
  modelPredictedOEFCandidateLevel : PromotionLevel
  aggregateEngagementSignalLevel : PromotionLevel
  reviewedResidualHypothesisLevel : PromotionLevel
  pedagogicalJPlusOneCandidateLevel : PromotionLevel
  evaluatedLocalInterventionLevel : PromotionLevel
  replicatedProgrammePracticeCandidateLevel : PromotionLevel

canonicalPromotionLevels : List PromotionLevel
canonicalPromotionLevels =
  rawFeedbackSurfaceLevel
  ∷ humanCodedOEFCandidateLevel
  ∷ modelPredictedOEFCandidateLevel
  ∷ aggregateEngagementSignalLevel
  ∷ reviewedResidualHypothesisLevel
  ∷ pedagogicalJPlusOneCandidateLevel
  ∷ evaluatedLocalInterventionLevel
  ∷ replicatedProgrammePracticeCandidateLevel
  ∷ []

record JPlusOneSafetyGate : Set where
  constructor mkJPlusOneSafetyGate
  field
    studentChoiceRequired : Bool
    studentChoiceRequiredIsTrue : studentChoiceRequired ≡ true
    contextualFitRequired : Bool
    contextualFitRequiredIsTrue : contextualFitRequired ≡ true
    lowBurdenRequired : Bool
    lowBurdenRequiredIsTrue : lowBurdenRequired ≡ true
    nonShamingRequired : Bool
    nonShamingRequiredIsTrue : nonShamingRequired ≡ true
    nonSurveillanceRequired : Bool
    nonSurveillanceRequiredIsTrue : nonSurveillanceRequired ≡ true
    humanInterpretationRequired : Bool
    humanInterpretationRequiredIsTrue : humanInterpretationRequired ≡ true
    measurableReviewRequired : Bool
    measurableReviewRequiredIsTrue : measurableReviewRequired ≡ true
    optOutRequired : Bool
    optOutRequiredIsTrue : optOutRequired ≡ true

open JPlusOneSafetyGate public

canonicalJPlusOneSafetyGate : JPlusOneSafetyGate
canonicalJPlusOneSafetyGate =
  mkJPlusOneSafetyGate
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl

data ResidualHypothesisKind : Set where
  lowDetectedSocialEngagement : ResidualHypothesisKind
  negativeBehaviouralEngagement : ResidualHypothesisKind
  negativeEmotionalEngagement : ResidualHypothesisKind
  lowDetectedCollaborativeEngagement : ResidualHypothesisKind
  classificationUncertaintyResidual : ResidualHypothesisKind
  nonresponseResidual : ResidualHypothesisKind
  ecologicalContextResidual : ResidualHypothesisKind

record PedagogicalHandleCandidate : Set where
  constructor mkPedagogicalHandleCandidate
  field
    handleLabel : String
    sourceResidual : ResidualHypothesisKind
    sourceOEFElement : OEF.OEFElement
    candidateHandles : List String
    safetyGate : JPlusOneSafetyGate
    handleCandidateOnly : Bool
    handleCandidateOnlyIsTrue : handleCandidateOnly ≡ true
    handleNotAutomatic : Bool
    handleNotAutomaticIsTrue : handleNotAutomatic ≡ true
    handleNotDiagnosis : Bool
    handleNotDiagnosisIsTrue : handleNotDiagnosis ≡ true
    handleNotCareProof : Bool
    handleNotCareProofIsTrue : handleNotCareProof ≡ true
    handleRequiresEvidenceReturn : Bool
    handleRequiresEvidenceReturnIsTrue : handleRequiresEvidenceReturn ≡ true

open PedagogicalHandleCandidate public

canonicalSocialHandleCandidate : PedagogicalHandleCandidate
canonicalSocialHandleCandidate =
  mkPedagogicalHandleCandidate
    "low detected social engagement candidate"
    lowDetectedSocialEngagement
    OEF.socialEngagement
    ( "peer introductions"
    ∷ "small discussion groups"
    ∷ "teacher presence"
    ∷ "informal forum"
    ∷ "study partnerships"
    ∷ [] )
    canonicalJPlusOneSafetyGate
    true refl
    true refl
    true refl
    true refl
    true refl

canonicalBehaviouralHandleCandidate : PedagogicalHandleCandidate
canonicalBehaviouralHandleCandidate =
  mkPedagogicalHandleCandidate
    "negative behavioural engagement candidate"
    negativeBehaviouralEngagement
    OEF.behaviouralEngagement
    ( "clearer navigation"
    ∷ "explicit expectations"
    ∷ "worked pathway"
    ∷ "agency support"
    ∷ "required versus optional distinction"
    ∷ [] )
    canonicalJPlusOneSafetyGate
    true refl
    true refl
    true refl
    true refl
    true refl

canonicalEmotionalHandleCandidate : PedagogicalHandleCandidate
canonicalEmotionalHandleCandidate =
  mkPedagogicalHandleCandidate
    "negative emotional engagement candidate"
    negativeEmotionalEngagement
    OEF.emotionalEngagement
    ( "expectation clarification"
    ∷ "human check-in"
    ∷ "reduced overload"
    ∷ "more processing time"
    ∷ "motivational support chosen by the student"
    ∷ [] )
    canonicalJPlusOneSafetyGate
    true refl
    true refl
    true refl
    true refl
    true refl

canonicalPedagogicalHandleCandidates : List PedagogicalHandleCandidate
canonicalPedagogicalHandleCandidates =
  canonicalSocialHandleCandidate
  ∷ canonicalBehaviouralHandleCandidate
  ∷ canonicalEmotionalHandleCandidate
  ∷ []

record EvidenceReturn : Set where
  constructor mkEvidenceReturn
  field
    returnLabel : String
    residualBeforeSurface : String
    residualAfterSurface : String
    participantInterpretationSurface : String
    outcomeReviewed : Bool
    outcomeReviewedIsTrue : outcomeReviewed ≡ true
    outcomeCandidateSuccess : Bool
    outcomeNoUniversalPromotion : Bool
    outcomeNoUniversalPromotionIsTrue : outcomeNoUniversalPromotion ≡ true
    outcomeWithdrawalAllowed : Bool
    outcomeWithdrawalAllowedIsTrue : outcomeWithdrawalAllowed ≡ true

open EvidenceReturn public

canonicalEvidenceReturn : EvidenceReturn
canonicalEvidenceReturn =
  mkEvidenceReturn
    "local pedagogical evidence-return receipt"
    "residual before candidate handle"
    "residual after candidate handle"
    "student and educator contextual interpretation"
    true refl
    false
    true refl
    true refl

data JPlusOnePromotionRoute : Set where
  reviewedCandidateRoute : JPlusOnePromotionRoute
  modelOutputEqualsInterventionRoute : JPlusOnePromotionRoute
  aggregateEqualsDiagnosisRoute : JPlusOnePromotionRoute
  nudgeEqualsCareRoute : JPlusOnePromotionRoute
  localSuccessEqualsUniversalPracticeRoute : JPlusOnePromotionRoute
  surveillanceEqualsSupportRoute : JPlusOnePromotionRoute

AdmissibleJPlusOnePromotionRoute : JPlusOnePromotionRoute → Set
AdmissibleJPlusOnePromotionRoute reviewedCandidateRoute = ⊤
AdmissibleJPlusOnePromotionRoute modelOutputEqualsInterventionRoute = Never
AdmissibleJPlusOnePromotionRoute aggregateEqualsDiagnosisRoute = Never
AdmissibleJPlusOnePromotionRoute nudgeEqualsCareRoute = Never
AdmissibleJPlusOnePromotionRoute localSuccessEqualsUniversalPracticeRoute = Never
AdmissibleJPlusOnePromotionRoute surveillanceEqualsSupportRoute = Never

reviewedCandidateRouteAdmissible :
  AdmissibleJPlusOnePromotionRoute reviewedCandidateRoute
reviewedCandidateRouteAdmissible = tt

modelOutputEqualsInterventionBlocked :
  AdmissibleJPlusOnePromotionRoute modelOutputEqualsInterventionRoute → Never
modelOutputEqualsInterventionBlocked ()

aggregateEqualsDiagnosisBlocked :
  AdmissibleJPlusOnePromotionRoute aggregateEqualsDiagnosisRoute → Never
aggregateEqualsDiagnosisBlocked ()

nudgeEqualsCareBlocked :
  AdmissibleJPlusOnePromotionRoute nudgeEqualsCareRoute → Never
nudgeEqualsCareBlocked ()

localSuccessEqualsUniversalPracticeBlocked :
  AdmissibleJPlusOnePromotionRoute localSuccessEqualsUniversalPracticeRoute → Never
localSuccessEqualsUniversalPracticeBlocked ()

surveillanceEqualsSupportBlocked :
  AdmissibleJPlusOnePromotionRoute surveillanceEqualsSupportRoute → Never
surveillanceEqualsSupportBlocked ()

record PedagogicalJPlusOneRouting : Set where
  constructor mkPedagogicalJPlusOneRouting
  field
    sourceSystem : OEF.OEFMultiFibreFeedbackHyperfabric
    sourceSystemIsCanonical : sourceSystem ≡ OEF.canonicalOEFMultiFibreFeedbackHyperfabric
    promotionLevels : List PromotionLevel
    promotionLevelsAreCanonical : promotionLevels ≡ canonicalPromotionLevels
    handleCandidates : List PedagogicalHandleCandidate
    handleCandidatesAreCanonical : handleCandidates ≡ canonicalPedagogicalHandleCandidates
    safetyGate : JPlusOneSafetyGate
    safetyGateIsCanonical : safetyGate ≡ canonicalJPlusOneSafetyGate
    evidenceReturn : EvidenceReturn
    evidenceReturnIsCanonical : evidenceReturn ≡ canonicalEvidenceReturn
    route : JPlusOnePromotionRoute
    routeIsReviewed : route ≡ reviewedCandidateRoute
    routeAdmissible : AdmissibleJPlusOnePromotionRoute route
    aiOutputRoutesAttention : Bool
    aiOutputRoutesAttentionIsTrue : aiOutputRoutesAttention ≡ true
    humanReviewRequired : Bool
    humanReviewRequiredIsTrue : humanReviewRequired ≡ true
    jPlusOneNotAutomatic : Bool
    jPlusOneNotAutomaticIsTrue : jPlusOneNotAutomatic ≡ true
    jPlusOneAgencySafe : Bool
    jPlusOneAgencySafeIsTrue : jPlusOneAgencySafe ≡ true
    replicatedPracticeRequiresReplication : Bool
    replicatedPracticeRequiresReplicationIsTrue : replicatedPracticeRequiresReplication ≡ true
    reading : String

open PedagogicalJPlusOneRouting public

canonicalPedagogicalJPlusOneRouting : PedagogicalJPlusOneRouting
canonicalPedagogicalJPlusOneRouting =
  mkPedagogicalJPlusOneRouting
    OEF.canonicalOEFMultiFibreFeedbackHyperfabric refl
    canonicalPromotionLevels refl
    canonicalPedagogicalHandleCandidates refl
    canonicalJPlusOneSafetyGate refl
    canonicalEvidenceReturn refl
    reviewedCandidateRoute refl tt
    true refl
    true refl
    true refl
    true refl
    true refl
    "AI output may route human investigation from a bounded engagement signal to a residual hypothesis and a small, reversible, agency-safe pedagogical candidate. It cannot issue an automatic intervention, diagnosis, care claim, surveillance mandate, or universal practice promotion."

AIOutputRoutesAttention : Set
AIOutputRoutesAttention =
  aiOutputRoutesAttention canonicalPedagogicalJPlusOneRouting ≡ true

aiOutputRoutesAttentionProof : AIOutputRoutesAttention
aiOutputRoutesAttentionProof =
  aiOutputRoutesAttentionIsTrue canonicalPedagogicalJPlusOneRouting

PedagogicalCandidateNotAutomaticIntervention : Set
PedagogicalCandidateNotAutomaticIntervention =
  jPlusOneNotAutomatic canonicalPedagogicalJPlusOneRouting ≡ true

pedagogicalCandidateNotAutomaticIntervention :
  PedagogicalCandidateNotAutomaticIntervention
pedagogicalCandidateNotAutomaticIntervention =
  jPlusOneNotAutomaticIsTrue canonicalPedagogicalJPlusOneRouting
