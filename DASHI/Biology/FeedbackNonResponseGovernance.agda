module DASHI.Biology.FeedbackNonResponseGovernance where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Biology.OEFMultiFibreFeedbackHyperfabric as OEF

------------------------------------------------------------------------
-- Voluntary feedback and non-response governance.
--
-- The observed distribution is conditional on response.  No-response is
-- not promoted to neutrality, satisfaction, disengagement, or a complete
-- student-voice claim.

data Never : Set where

data ResponseState : Set where
  respondedPositive : ResponseState
  respondedNegative : ResponseState
  respondedMixed : ResponseState
  respondedNeutral : ResponseState
  noResponse : ResponseState

canonicalResponseStates : List ResponseState
canonicalResponseStates =
  respondedPositive
  ∷ respondedNegative
  ∷ respondedMixed
  ∷ respondedNeutral
  ∷ noResponse
  ∷ []

data ResponseClaimRoute : Set where
  conditionalRespondentSurfaceRoute : ResponseClaimRoute
  noResponseEqualsNeutralRoute : ResponseClaimRoute
  noResponseEqualsSatisfiedRoute : ResponseClaimRoute
  noResponseEqualsDisengagedRoute : ResponseClaimRoute
  respondentsEqualCohortRoute : ResponseClaimRoute
  surveyEqualsCompleteVoiceRoute : ResponseClaimRoute

AdmissibleResponseClaimRoute : ResponseClaimRoute → Set
AdmissibleResponseClaimRoute conditionalRespondentSurfaceRoute = ⊤
AdmissibleResponseClaimRoute noResponseEqualsNeutralRoute = Never
AdmissibleResponseClaimRoute noResponseEqualsSatisfiedRoute = Never
AdmissibleResponseClaimRoute noResponseEqualsDisengagedRoute = Never
AdmissibleResponseClaimRoute respondentsEqualCohortRoute = Never
AdmissibleResponseClaimRoute surveyEqualsCompleteVoiceRoute = Never

conditionalRespondentSurfaceRouteAdmissible :
  AdmissibleResponseClaimRoute conditionalRespondentSurfaceRoute
conditionalRespondentSurfaceRouteAdmissible = tt

noResponseEqualsNeutralBlocked :
  AdmissibleResponseClaimRoute noResponseEqualsNeutralRoute → Never
noResponseEqualsNeutralBlocked ()

noResponseEqualsSatisfiedBlocked :
  AdmissibleResponseClaimRoute noResponseEqualsSatisfiedRoute → Never
noResponseEqualsSatisfiedBlocked ()

noResponseEqualsDisengagedBlocked :
  AdmissibleResponseClaimRoute noResponseEqualsDisengagedRoute → Never
noResponseEqualsDisengagedBlocked ()

respondentsEqualCohortBlocked :
  AdmissibleResponseClaimRoute respondentsEqualCohortRoute → Never
respondentsEqualCohortBlocked ()

surveyEqualsCompleteVoiceBlocked :
  AdmissibleResponseClaimRoute surveyEqualsCompleteVoiceRoute → Never
surveyEqualsCompleteVoiceBlocked ()

record FeedbackSampleReceipt : Set where
  constructor mkFeedbackSampleReceipt
  field
    sampleLabel : String
    labelledTrainingFeedbackSentiments : Nat
    laterTestingFeedbackSentiments : Nat
    fullEnrolledCohortCountKnown : Bool
    fullEnrolledCohortCountKnownIsFalse : fullEnrolledCohortCountKnown ≡ false
    voluntaryResponseSurface : Bool
    voluntaryResponseSurfaceIsTrue : voluntaryResponseSurface ≡ true
    respondentConditionalDistribution : Bool
    respondentConditionalDistributionIsTrue : respondentConditionalDistribution ≡ true
    respondentDistributionNotCohortDistribution : Bool
    respondentDistributionNotCohortDistributionIsTrue : respondentDistributionNotCohortDistribution ≡ true
    nonresponseUndetermined : Bool
    nonresponseUndeterminedIsTrue : nonresponseUndetermined ≡ true
    notes : List String

open FeedbackSampleReceipt public

canonicalFeedbackSampleReceipt : FeedbackSampleReceipt
canonicalFeedbackSampleReceipt =
  mkFeedbackSampleReceipt
    "OEF AI voluntary-feedback sample receipt"
    383
    311
    false refl
    true refl
    true refl
    true refl
    true refl
    ( "The counts are feedback sentiments used for training and testing, not an asserted enrolled-cohort denominator."
    ∷ "Observed OEF distributions are conditional on voluntary end-of-course response."
    ∷ "Silent students remain unresolved rather than neutral, satisfied, or disengaged."
    ∷ [] )

record FeedbackNonResponseGovernance : Set where
  constructor mkFeedbackNonResponseGovernance
  field
    sourceSystem : OEF.OEFMultiFibreFeedbackHyperfabric
    sourceSystemIsCanonical : sourceSystem ≡ OEF.canonicalOEFMultiFibreFeedbackHyperfabric
    responseStates : List ResponseState
    responseStatesAreCanonical : responseStates ≡ canonicalResponseStates
    sampleReceipt : FeedbackSampleReceipt
    sampleReceiptIsCanonical : sampleReceipt ≡ canonicalFeedbackSampleReceipt
    route : ResponseClaimRoute
    routeIsConditional : route ≡ conditionalRespondentSurfaceRoute
    routeAdmissible : AdmissibleResponseClaimRoute route
    noResponseNotNeutral : Bool
    noResponseNotNeutralIsTrue : noResponseNotNeutral ≡ true
    noResponseNotSatisfied : Bool
    noResponseNotSatisfiedIsTrue : noResponseNotSatisfied ≡ true
    noResponseNotDisengaged : Bool
    noResponseNotDisengagedIsTrue : noResponseNotDisengaged ≡ true
    respondentSampleNotCohort : Bool
    respondentSampleNotCohortIsTrue : respondentSampleNotCohort ≡ true
    surveyNotCompleteVoice : Bool
    surveyNotCompleteVoiceIsTrue : surveyNotCompleteVoice ≡ true
    reading : String

open FeedbackNonResponseGovernance public

canonicalFeedbackNonResponseGovernance : FeedbackNonResponseGovernance
canonicalFeedbackNonResponseGovernance =
  mkFeedbackNonResponseGovernance
    OEF.canonicalOEFMultiFibreFeedbackHyperfabric refl
    canonicalResponseStates refl
    canonicalFeedbackSampleReceipt refl
    conditionalRespondentSurfaceRoute refl tt
    true refl
    true refl
    true refl
    true refl
    true refl
    "The paper's end-of-course feedback is a voluntary respondent surface. The classifier estimates OEF patterns conditional on response; no-response remains an unresolved fibre and cannot be converted into cohort-level student voice."

NonResponseRemainsUndetermined : Set
NonResponseRemainsUndetermined =
  nonresponseUndetermined canonicalFeedbackSampleReceipt ≡ true

nonResponseRemainsUndetermined : NonResponseRemainsUndetermined
nonResponseRemainsUndetermined =
  nonresponseUndeterminedIsTrue canonicalFeedbackSampleReceipt

RespondentSampleNotCohort : Set
RespondentSampleNotCohort =
  respondentSampleNotCohort canonicalFeedbackNonResponseGovernance ≡ true

respondentSampleNotCohortProof : RespondentSampleNotCohort
respondentSampleNotCohortProof =
  respondentSampleNotCohortIsTrue canonicalFeedbackNonResponseGovernance
