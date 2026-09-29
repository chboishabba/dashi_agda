{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTCommonRegimeBidiAttemptExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.CommonRegimeMathematicalCoreExact as Core

------------------------------------------------------------------------
-- EXECUTABLE COMMON-REGIME / BACKREACTION / CORRECTION ATTEMPT
------------------------------------------------------------------------

andBool : Bool → Bool → Bool
andBool true true = true
andBool _ _ = false

record CommonRegimeDecisionProbe (U : Weld.UnifiedCandidate) : Set₁ where
  field
    grRegimeDecision :
      Weld.Regime U → Bool
    qftRegimeDecision :
      Weld.Regime U → Bool

    backreactionDecision :
      Weld.Candidate U → Weld.Regime U → Bool
    correctionDecision :
      Weld.Candidate U → Weld.Regime U → Bool

    grRegimeSound :
      ∀ regime →
      grRegimeDecision regime ≡ true →
      Weld.grRegime U regime

    qftRegimeSound :
      ∀ regime →
      qftRegimeDecision regime ≡ true →
      Weld.qftRegime U regime

    backreactionSound :
      ∀ candidate regime →
      backreactionDecision candidate regime ≡ true →
      Weld.BackreactionConsistent U
        (Weld.coarseGrain U candidate regime) regime

    correctionSound :
      ∀ candidate regime →
      correctionDecision candidate regime ≡ true →
      Weld.CorrectionsControlled U
        (Weld.coarseGrain U candidate regime) regime

open CommonRegimeDecisionProbe public

record CommonRegimeAttemptResult
    (U : Weld.UnifiedCandidate)
    (probe : CommonRegimeDecisionProbe U)
    (candidate : Weld.Candidate U)
    (regime : Weld.Regime U) : Set where
  constructor commonRegimeAttemptResult
  field
    grPassed : Bool
    qftPassed : Bool
    backreactionPassed : Bool
    correctionPassed : Bool
    allPassed : Bool

    grPassedIsComputed :
      grPassed ≡ grRegimeDecision probe regime
    qftPassedIsComputed :
      qftPassed ≡ qftRegimeDecision probe regime
    backreactionPassedIsComputed :
      backreactionPassed ≡ backreactionDecision probe candidate regime
    correctionPassedIsComputed :
      correctionPassed ≡ correctionDecision probe candidate regime

    allPassedIsComputed :
      allPassed
      ≡ andBool grPassed
          (andBool qftPassed
            (andBool backreactionPassed correctionPassed))

open CommonRegimeAttemptResult public

runCommonRegimeAttempt :
  ∀ {U : Weld.UnifiedCandidate}
    (probe : CommonRegimeDecisionProbe U)
    (candidate : Weld.Candidate U)
    (regime : Weld.Regime U) →
  CommonRegimeAttemptResult U probe candidate regime
runCommonRegimeAttempt probe candidate regime =
  commonRegimeAttemptResult
    (grRegimeDecision probe regime)
    (qftRegimeDecision probe regime)
    (backreactionDecision probe candidate regime)
    (correctionDecision probe candidate regime)
    (andBool
      (grRegimeDecision probe regime)
      (andBool
        (qftRegimeDecision probe regime)
        (andBool
          (backreactionDecision probe candidate regime)
          (correctionDecision probe candidate regime))))
    refl refl refl refl refl

record PassingCommonRegimeAttempt
    (U : Weld.UnifiedCandidate)
    (probe : CommonRegimeDecisionProbe U)
    (regime : Weld.Regime U) : Set₁ where
  field
    grPass :
      grRegimeDecision probe regime ≡ true

    qftPass :
      qftRegimeDecision probe regime ≡ true

    backreactionPass :
      ∀ candidate →
      backreactionDecision probe candidate regime ≡ true

    correctionPass :
      ∀ candidate →
      correctionDecision probe candidate regime ≡ true

open PassingCommonRegimeAttempt public

passingAttemptBuildsCommonRegimeCore :
  ∀ {U : Weld.UnifiedCandidate}
    {probe : CommonRegimeDecisionProbe U}
    {regime : Weld.Regime U} →
  PassingCommonRegimeAttempt U probe regime →
  Core.CommonRegimeMathematicalCore U
passingAttemptBuildsCommonRegimeCore {probe = probe} {regime = regime} pass =
  record
    { Core.CommonRegimeMathematicalCore.overlapRegime =
        regime
    ; Core.CommonRegimeMathematicalCore.overlapIsGR =
        grRegimeSound probe regime (grPass pass)
    ; Core.CommonRegimeMathematicalCore.overlapIsQFT =
        qftRegimeSound probe regime (qftPass pass)
    ; Core.CommonRegimeMathematicalCore.backreactionConsistency =
        λ candidate →
          backreactionSound probe candidate regime
            (backreactionPass pass candidate)
    ; Core.CommonRegimeMathematicalCore.correctionControl =
        λ candidate →
          correctionSound probe candidate regime
            (correctionPass pass candidate)
    }

missingCommonRegimePromotionTokenBlocksAttemptExecution : Bool
missingCommonRegimePromotionTokenBlocksAttemptExecution = false

missingCommonRegimePromotionTokenBlocksAttemptExecutionIsFalse :
  missingCommonRegimePromotionTokenBlocksAttemptExecution ≡ false
missingCommonRegimePromotionTokenBlocksAttemptExecutionIsFalse = refl

commonRegimeAttemptRetainsFourSeparateFailureCoordinates : Bool
commonRegimeAttemptRetainsFourSeparateFailureCoordinates = true

commonRegimeAttemptRetainsFourSeparateFailureCoordinatesIsTrue :
  commonRegimeAttemptRetainsFourSeparateFailureCoordinates ≡ true
commonRegimeAttemptRetainsFourSeparateFailureCoordinatesIsTrue = refl
