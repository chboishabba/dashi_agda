module DASHI.Physics.Closure.YMDepthAsContinuumLimitReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Yang-Mills depth-as-continuum-limit receipt.

data YMDepthAsContinuumLimitStatus : Set where
  depthContinuumLimitCandidateRecordedNoClay :
    YMDepthAsContinuumLimitStatus

data YMDepthContinuumLimitStep : Set where
  depthCarrierApproximants :
    YMDepthContinuumLimitStep

  alphaOnePowerFrequencyResolution :
    YMDepthContinuumLimitStep

  depthInfinityMomentumContinuumLimit :
    YMDepthContinuumLimitStep

  cutoffMeasureTightnessCriterion :
    YMDepthContinuumLimitStep

  uvCutoffPathIntegralRenormalisability :
    YMDepthContinuumLimitStep

  perturbativeFourDimensionalYangMillsAuthority :
    YMDepthContinuumLimitStep

  nonPerturbativeTightnessCandidate :
    YMDepthContinuumLimitStep

canonicalYMDepthContinuumLimitSteps :
  List YMDepthContinuumLimitStep
canonicalYMDepthContinuumLimitSteps =
  depthCarrierApproximants
  ∷ alphaOnePowerFrequencyResolution
  ∷ depthInfinityMomentumContinuumLimit
  ∷ cutoffMeasureTightnessCriterion
  ∷ uvCutoffPathIntegralRenormalisability
  ∷ perturbativeFourDimensionalYangMillsAuthority
  ∷ nonPerturbativeTightnessCandidate
  ∷ []

data YMRenormalisabilityCitation : Set where
  tHooft1972 :
    YMRenormalisabilityCitation

data YMRenormalisabilityAuthority : Set where
  citationAuthority :
    YMRenormalisabilityCitation →
    YMRenormalisabilityAuthority

data YMDepthContinuumLimitPromotion : Set where

ymDepthContinuumLimitPromotionImpossibleHere :
  YMDepthContinuumLimitPromotion →
  ⊥
ymDepthContinuumLimitPromotionImpossibleHere ()

depthFrequencyResolutionStatement : String
depthFrequencyResolutionStatement =
  "At depth d, carrier approximants resolve frequencies up to alpha1^{-d}; d -> infinity is a momentum-space continuum limit."

tightnessRenormalisabilityStatement : String
tightnessRenormalisabilityStatement =
  "Tightness of measures mu_d as d -> infinity is equivalent to UV-cutoff path integral convergence/renormalisability."

ymDepthContinuumLimitStatement : String
ymDepthContinuumLimitStatement =
  "4D Yang-Mills perturbative renormalisability is recorded by citationAuthority tHooft1972, while non-perturbative tightness remains candidate-only; Clay Yang-Mills remains false."

record YMDepthAsContinuumLimitReceipt : Setω where
  field
    status :
      YMDepthAsContinuumLimitStatus

    continuumLimitSteps :
      List YMDepthContinuumLimitStep

    continuumLimitStepsAreCanonical :
      continuumLimitSteps ≡ canonicalYMDepthContinuumLimitSteps

    depthResolutionStatement :
      String

    depthResolutionStatementIsCanonical :
      depthResolutionStatement ≡ depthFrequencyResolutionStatement

    tightnessStatement :
      String

    tightnessStatementIsCanonical :
      tightnessStatement ≡ tightnessRenormalisabilityStatement

    statement :
      String

    statementIsCanonical :
      statement ≡ ymDepthContinuumLimitStatement

    ymRenormalisabilityAuthority :
      YMRenormalisabilityAuthority

    ymRenormalisabilityAuthorityIsTHooft1972 :
      ymRenormalisabilityAuthority ≡ citationAuthority tHooft1972

    ymDepthContinuumLimit :
      Bool

    ymDepthContinuumLimitIsTrue :
      ymDepthContinuumLimit ≡ true

    momentumSpaceLimit :
      Bool

    momentumSpaceLimitIsTrue :
      momentumSpaceLimit ≡ true

    tightnessEquivalentToRenormalisability :
      Bool

    tightnessEquivalentToRenormalisabilityIsTrue :
      tightnessEquivalentToRenormalisability ≡ true

    ymRenormalisable4D :
      Bool

    ymRenormalisable4DIsCitationAuthorityTrue :
      ymRenormalisable4D ≡ true

    ymL3ViaDepth :
      Bool

    ymL3ViaDepthIsCandidateTrue :
      ymL3ViaDepth ≡ true

    nonPerturbativeTightnessProved :
      Bool

    nonPerturbativeTightnessProvedIsFalse :
      nonPerturbativeTightnessProved ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    promotionFlags :
      List YMDepthContinuumLimitPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open YMDepthAsContinuumLimitReceipt public

canonicalYMDepthAsContinuumLimitReceipt :
  YMDepthAsContinuumLimitReceipt
canonicalYMDepthAsContinuumLimitReceipt =
  record
    { status =
        depthContinuumLimitCandidateRecordedNoClay
    ; continuumLimitSteps =
        canonicalYMDepthContinuumLimitSteps
    ; continuumLimitStepsAreCanonical =
        refl
    ; depthResolutionStatement =
        depthFrequencyResolutionStatement
    ; depthResolutionStatementIsCanonical =
        refl
    ; tightnessStatement =
        tightnessRenormalisabilityStatement
    ; tightnessStatementIsCanonical =
        refl
    ; statement =
        ymDepthContinuumLimitStatement
    ; statementIsCanonical =
        refl
    ; ymRenormalisabilityAuthority =
        citationAuthority tHooft1972
    ; ymRenormalisabilityAuthorityIsTHooft1972 =
        refl
    ; ymDepthContinuumLimit =
        true
    ; ymDepthContinuumLimitIsTrue =
        refl
    ; momentumSpaceLimit =
        true
    ; momentumSpaceLimitIsTrue =
        refl
    ; tightnessEquivalentToRenormalisability =
        true
    ; tightnessEquivalentToRenormalisabilityIsTrue =
        refl
    ; ymRenormalisable4D =
        true
    ; ymRenormalisable4DIsCitationAuthorityTrue =
        refl
    ; ymL3ViaDepth =
        true
    ; ymL3ViaDepthIsCandidateTrue =
        refl
    ; nonPerturbativeTightnessProved =
        false
    ; nonPerturbativeTightnessProvedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Depth d carrier approximants resolve frequencies up to alpha1^{-d}"
        ∷ "The d -> infinity passage is recorded as a momentum-space continuum limit"
        ∷ "Tightness of mu_d is recorded as equivalent to UV-cutoff path integral convergence/renormalisability"
        ∷ "4D YM perturbative renormalisability is citationAuthority tHooft1972"
        ∷ "Non-perturbative tightness remains candidate-only"
        ∷ "No Clay Yang-Mills or terminal Clay promotion follows"
        ∷ []
    }

ymDepthAsContinuumLimitKeepsNonPerturbativeTightnessFalse :
  nonPerturbativeTightnessProved
    canonicalYMDepthAsContinuumLimitReceipt ≡ false
ymDepthAsContinuumLimitKeepsNonPerturbativeTightnessFalse =
  refl

ymDepthAsContinuumLimitKeepsClayFalse :
  clayYangMillsPromoted
    canonicalYMDepthAsContinuumLimitReceipt ≡ false
ymDepthAsContinuumLimitKeepsClayFalse =
  refl

ymDepthAsContinuumLimitKeepsTerminalFalse :
  terminalClayClaimPromoted
    canonicalYMDepthAsContinuumLimitReceipt ≡ false
ymDepthAsContinuumLimitKeepsTerminalFalse =
  refl
