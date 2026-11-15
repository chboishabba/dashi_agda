{-# OPTIONS --safe #-}
module DASHI.Physics.Motors.MadScience369V2FinitePowerDiscriminatorsExact where

-- FINITE ARITHMETIC / EPISTEMIC COUNTERMODELS ONLY.
-- Attribution: madscience369 Instagram V2, transcript supplied 2026-11-14.
-- No pulse/coil count or topology is established by this transcript.
-- Independently constructed finite accounting examples, not observations.
-- Reuse candidates: KSW668FiniteDiscriminatorsExact;
-- ResonantFlightHarmonicPowerPhaseExact;
-- Resonate369SchematicAdmissionExact (different designer/device).

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

data ⊥ : Set where

-- Distinguish claim, filmed display, and physically verified readings.
data EvidenceStage : Set where
  attributedSpeech videoDisplay calibratedReproduction : EvidenceStage

record AttributedV2Claim : Set where
  constructor v2-claim
  field
    attribution : EvidenceStage
    nominalInputW nominalOutputW nominalRPM : Nat
    pulseTopologyEstablished : Bool

reelClaim : AttributedV2Claim
reelClaim = v2-claim attributedSpeech 286 45 2354 false

pulseTopologyNotEstablished :
  AttributedV2Claim.pulseTopologyEstablished reelClaim ≡ false
pulseTopologyNotEstablished = refl

-- Finite steady-state counterexample: identical gross input and nonnegative
-- output coexist with changing OTHER loss budget. Nothing here asserts that
-- a real V2 motor does so or that its losses really are 286 W / 241 W.
record NonnegativePowerPartition : Set where
  constructor partition
  field
    input output other : Nat
    closes : input ≡ output + other

unloadedIllustration : NonnegativePowerPartition
unloadedIllustration = partition 286 0 286 refl

loadedIllustration : NonnegativePowerPartition
loadedIllustration = partition 286 45 241 refl

sameDisplayedInput :
  NonnegativePowerPartition.input unloadedIllustration
  ≡ NonnegativePowerPartition.input loadedIllustration
sameDisplayedInput = refl

outputChanges :
  NonnegativePowerPartition.output loadedIllustration ≡ 45
outputChanges = refl

otherBudgetChanges :
  NonnegativePowerPartition.other loadedIllustration ≡ 241
otherBudgetChanges = refl

-- Different physical explanations can project to the same coarse display.
-- These worlds are distinguishable only by further sensors/interventions.
data Explanation : Set where
  lossCompensation temporaryStorage measurementMismatch : Explanation

record ObservationWorld : Set where
  constructor world
  field
    explanation : Explanation
    displayedInput : Nat
    displayedOutput : Nat

worldLoss : ObservationWorld
worldLoss = world lossCompensation 286 45

worldStorage : ObservationWorld
worldStorage = world temporaryStorage 286 45

sameCoarseInput :
  ObservationWorld.displayedInput worldLoss
  ≡ ObservationWorld.displayedInput worldStorage
sameCoarseInput = refl

sameCoarseOutput :
  ObservationWorld.displayedOutput worldLoss
  ≡ ObservationWorld.displayedOutput worldStorage
sameCoarseOutput = refl

lossIsNotStorage : lossCompensation ≡ temporaryStorage → ⊥
lossIsNotStorage ()

-- This is the key identifiability no-go, not a finding about the device.
coarseObservationCannotUniquelyIdentifyMechanism :
  (classify : Nat → Nat → Explanation) →
  classify 286 45 ≡ lossCompensation →
  classify 286 45 ≡ temporaryStorage → ⊥
coarseObservationCannotUniquelyIdentifyMechanism classify a b =
  lossIsNotStorage (trans (sym a) b)
  where
    sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
    sym refl = refl
    trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
    trans refl yz = yz

-- Energy per time window, for a hypothetical continuously supplied 45 W.
-- Durations are test conditions, NOT timestamps established in the reel.
energyForSeconds : Nat → Nat
energyForSeconds seconds = 45 * seconds

tenSecondEnergyJ : energyForSeconds 10 ≡ 450
tenSecondEnergyJ = refl

thirtySecondEnergyJ : energyForSeconds 30 ≡ 1350
thirtySecondEnergyJ = refl

sixtySecondEnergyJ : energyForSeconds 60 ≡ 2700
sixtySecondEnergyJ = refl