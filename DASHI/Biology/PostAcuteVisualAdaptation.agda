module DASHI.Biology.PostAcuteVisualAdaptation where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Two-timescale post-acute visual adaptation.
--
-- Fast perceptual state and slow adaptive state are separated.  Returning the
-- acute parameter to baseline does not force the complete system to return to
-- its pre-exposure response when the slow state has changed.
--
-- Source-facing reference:
-- Otto Simonsson et al.,
-- "Longitudinal associations between psychedelic use and unusual visual
-- experiences in the United States and the United Kingdom",
-- DOI 10.1177/02698811231218931.

data ExposureParameter : Set where
  baselineExposure : ExposureParameter
  acuteExposure : ExposureParameter

record FastSlowVisualState : Set where
  constructor fastSlowVisualState
  field
    fastPercept : Nat
    slowAdaptation : Nat

open FastSlowVisualState public

visualResponse :
  ExposureParameter → FastSlowVisualState → Nat
visualResponse baselineExposure s =
  fastPercept s + slowAdaptation s
visualResponse acuteExposure s =
  suc (suc (fastPercept s + slowAdaptation s))

preExposureState : FastSlowVisualState
preExposureState =
  fastSlowVisualState 1 0

postExposureAdaptedState : FastSlowVisualState
postExposureAdaptedState =
  fastSlowVisualState 1 1

sameBaselineParameterBeforeAndAfter :
  baselineExposure ≡ baselineExposure
sameBaselineParameterBeforeAndAfter = refl

baselineParameterDoesNotEraseSlowState :
  visualResponse baselineExposure preExposureState ≡ 1
  ×
  visualResponse baselineExposure postExposureAdaptedState ≡ 2
baselineParameterDoesNotEraseSlowState = refl , refl

data ExperienceHistory : Set where
  firstExposureHistory : ExperienceHistory
  experiencedHistory : ExperienceHistory

candidateAdaptationGain : ExperienceHistory → Nat
candidateAdaptationGain firstExposureHistory = 2
candidateAdaptationGain experiencedHistory = 1

firstExposureCandidateGainIsLarger :
  candidateAdaptationGain experiencedHistory
  ≤
  candidateAdaptationGain firstExposureHistory
firstExposureCandidateGainIsLarger =
  s≤s z≤n

record PostAcuteVisualBoundary : Set where
  constructor postAcuteVisualBoundary
  field
    associationEstablishesUniversalCausation : Bool
    associationEstablishesUniversalCausationIsFalse :
      associationEstablishesUniversalCausation ≡ false

    unusualVisualExperienceEqualsHPPD : Bool
    unusualVisualExperienceEqualsHPPDIsFalse :
      unusualVisualExperienceEqualsHPPD ≡ false

    candidateGainIsClinicalEffectSize : Bool
    candidateGainIsClinicalEffectSizeIsFalse :
      candidateGainIsClinicalEffectSize ≡ false

open PostAcuteVisualBoundary public

canonicalPostAcuteVisualBoundary : PostAcuteVisualBoundary
canonicalPostAcuteVisualBoundary =
  postAcuteVisualBoundary false refl false refl false refl
