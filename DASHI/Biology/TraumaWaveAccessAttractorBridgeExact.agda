module DASHI.Biology.TraumaWaveAccessAttractorBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Biology.PredictiveMetastabilityTraumaBridge as Predictive
import DASHI.Biology.TraumaMemoryAttractorPortfolio as Portfolio
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PNF.PNFFastAccessMemoryLearningBridgeExact as AccessMemory

------------------------------------------------------------------------
-- Structural, non-diagnostic bridge:
-- retained memories may coexist with a learned/context-sensitive fast-access
-- geometry that repeatedly recruits one memory lane more readily than another.
-- This is a candidate producer for attractor persistence, not a clinical test.
------------------------------------------------------------------------

data ControlLearningState : Set where
  flexibleControl threatBiasedControl : ControlLearningState

data CueContext : Set where
  ambiguousCue explicitSafetyCue : CueContext

record AccessProfile : Set where
  constructor accessProfile
  field
    threatAccessible : Bool
    safetyAccessible : Bool

open AccessProfile public

controlProfile : ControlLearningState → CueContext → AccessProfile
controlProfile flexibleControl ambiguousCue = accessProfile true true
controlProfile flexibleControl explicitSafetyCue = accessProfile false true
controlProfile threatBiasedControl ambiguousCue = accessProfile true false
controlProfile threatBiasedControl explicitSafetyCue = accessProfile false true

biasedCueClosesSafetyAccess :
  safetyAccessible (controlProfile threatBiasedControl ambiguousCue) ≡ false
biasedCueClosesSafetyAccess = refl

flexibleCueRetainsSafetyAccess :
  safetyAccessible (controlProfile flexibleControl ambiguousCue) ≡ true
flexibleCueRetainsSafetyAccess = refl

sameCueDifferentLearnedControl :
  safetyAccessible (controlProfile threatBiasedControl ambiguousCue)
  ≡ safetyAccessible (controlProfile flexibleControl ambiguousCue) → ⊥
sameCueDifferentLearnedControl ()

record RetainedThreatSafetyPair : Set where
  constructor retainedThreatSafetyPair
  field
    threatMemory safetyMemory : Memory.MemoryFibre

open RetainedThreatSafetyPair public

record SameMemoriesDifferentControlGeometry : Set where
  constructor sameMemoriesDifferentControlGeometry
  field
    memories : RetainedThreatSafetyPair
    firstControl secondControl : ControlLearningState
    cue : CueContext
    firstProfile secondProfile : AccessProfile
    firstProfile-v : firstProfile ≡ controlProfile firstControl cue
    secondProfile-v : secondProfile ≡ controlProfile secondControl cue
    safetyAccessDiffers :
      safetyAccessible firstProfile ≡ safetyAccessible secondProfile → ⊥

sameRetainedMemoriesCanHaveDifferentAccessGeometry :
  (threat safety : Memory.MemoryFibre) →
  SameMemoriesDifferentControlGeometry
sameRetainedMemoriesCanHaveDifferentAccessGeometry threat safety =
  sameMemoriesDifferentControlGeometry
    (retainedThreatSafetyPair threat safety)
    threatBiasedControl flexibleControl ambiguousCue
    (controlProfile threatBiasedControl ambiguousCue)
    (controlProfile flexibleControl ambiguousCue)
    refl refl (λ ())

------------------------------------------------------------------------
-- Existing trauma/attractor owners remain authoritative.
------------------------------------------------------------------------

predictiveBridge : Predictive.PredictiveMetastabilityTraumaBridge
predictiveBridge = Predictive.canonicalPredictiveMetastabilityTraumaBridge

trackedPolicyDeformation : Portfolio.TraumaPolicyDeformation
trackedPolicyDeformation = Portfolio.threatAttractorSubstitution

extinctionStillPreservesThreatEvent :
  (m : Memory.MemoryFibre) →
  Memory.rememberedEvent (Memory.extinguishActionDominance m)
  ≡ Memory.rememberedEvent m
extinctionStillPreservesThreatEvent =
  AccessMemory.extinctionPreservesRememberedPNF

extinctionChangesControlNotContent :
  (m : Memory.MemoryFibre) →
  Memory.actionWeight (Memory.extinguishActionDominance m)
  ≡ Agda.Builtin.Nat.zero
extinctionChangesControlNotContent =
  AccessMemory.extinctionZerosActionWeight

record TraumaWaveAccessBoundary : Set where
  constructor traumaWaveAccessBoundary
  field
    threatBiasedAccessProvesTrauma : Bool
    triggerLikeAccessContrastProvesHistoricalCause : Bool
    retainedThreatMemoryMeansCurrentThreatIsTrue : Bool
    extinctionErasesMemory : Bool
    waveAccessModelHasClinicalAuthority : Bool

canonicalTraumaWaveAccessBoundary : TraumaWaveAccessBoundary
canonicalTraumaWaveAccessBoundary =
  traumaWaveAccessBoundary false false false false false
