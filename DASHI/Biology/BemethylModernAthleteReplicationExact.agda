module DASHI.Biology.BemethylModernAthleteReplicationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record ModernAthleteReplication : Set where
  field
    publicationYear : String
    doi : String
    participantCount : Nat
    metaprotArmSize : Nat
    placeboArmSize : Nat
    studyDurationDays : Nat

    randomized : Bool
    doubleBlind : Bool
    placeboControlled : Bool
    pureMetaprotArmPresent : Bool

    metaprotCapsuleMg : Nat
    metaprotDailyDoseMg : Nat
    pwc170Measured : Bool
    lactateMeasured : Bool
    biochemicalRecoveryMeasured : Bool

    directMetaprotVsPlaceboEffectEstimateRecovered : Bool
    directMetaprotVsPlaceboSignificanceRecovered : Bool
    participantLevelExposureMeasured : Bool
    independentExternalReplicationPaid : Bool

    reading : String

open ModernAthleteReplication public

canonicalModernAthleteReplication : ModernAthleteReplication
canonicalModernAthleteReplication = record
  { publicationYear = "2023"
  ; doi = "10.17816/RCF567787"
  ; participantCount = 104
  ; metaprotArmSize = 18
  ; placeboArmSize = 16
  ; studyDurationDays = 15
  ; randomized = true
  ; doubleBlind = true
  ; placeboControlled = true
  ; pureMetaprotArmPresent = true
  ; metaprotCapsuleMg = 250
  ; metaprotDailyDoseMg = 1000
  ; pwc170Measured = true
  ; lactateMeasured = true
  ; biochemicalRecoveryMeasured = true
  ; directMetaprotVsPlaceboEffectEstimateRecovered = false
  ; directMetaprotVsPlaceboSignificanceRecovered = false
  ; participantLevelExposureMeasured = false
  ; independentExternalReplicationPaid = false
  ; reading = "A 2023 randomized double-blind placebo-controlled Russian athlete study contains a pure Metaprot arm and measures PWC170 plus metabolic recovery. This pays modern randomized same-compound evidence, but the recovered paper surface does not yet provide a direct Metaprot-vs-placebo effect estimate/significance receipt, participant-level exposure, or geographically/institutionally independent external replication."
  }

modernRandomizedDesignPaid : randomized canonicalModernAthleteReplication ≡ true
modernRandomizedDesignPaid = refl

modernPlaceboDesignPaid : placeboControlled canonicalModernAthleteReplication ≡ true
modernPlaceboDesignPaid = refl

directBetweenGroupEffectStillOpen :
  directMetaprotVsPlaceboEffectEstimateRecovered canonicalModernAthleteReplication ≡ false
directBetweenGroupEffectStillOpen = refl

randomizedDesignDoesNotEqualIndependentReplication :
  independentExternalReplicationPaid canonicalModernAthleteReplication ≡ false
randomizedDesignDoesNotEqualIndependentReplication = refl
