module DASHI.Biology.AvianMagnetoreceptionCueFusion where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Exact finite cue-substitution witness motivated by the Lisowski et al.
-- context interaction: macrophage depletion disrupts orientation under
-- overcast conditions, while orientation is retained when the sun is visible.
--
-- This is a policy-shape witness, not a claim that the real pigeon policy is
-- exhausted by these two cues.
------------------------------------------------------------------------

data NavigationContext : Set where
  overcastContext : NavigationContext
  sunVisibleContext : NavigationContext

data MacrophageState : Set where
  macrophagesIntact : MacrophageState
  macrophagesDepleted : MacrophageState

data CueSource : Set where
  magneticCue : CueSource
  solarCue : CueSource
  landmarkCue : CueSource
  memoryCue : CueSource
  otherCue : CueSource

data CuePolicyOutcome : Set where
  magneticCueUsed : CuePolicyOutcome
  solarCueUsed : CuePolicyOutcome
  orientationDegraded : CuePolicyOutcome

cuePolicy :
  NavigationContext ->
  MacrophageState ->
  CuePolicyOutcome
cuePolicy overcastContext macrophagesIntact = magneticCueUsed
cuePolicy overcastContext macrophagesDepleted = orientationDegraded
cuePolicy sunVisibleContext macrophagesIntact = solarCueUsed
cuePolicy sunVisibleContext macrophagesDepleted = solarCueUsed

overcastDepletionChangesPolicy :
  cuePolicy overcastContext macrophagesDepleted ≡ orientationDegraded
overcastDepletionChangesPolicy = refl

overcastIntactUsesMagneticCue :
  cuePolicy overcastContext macrophagesIntact ≡ magneticCueUsed
overcastIntactUsesMagneticCue = refl

sunVisibleIntactUsesSolarCue :
  cuePolicy sunVisibleContext macrophagesIntact ≡ solarCueUsed
sunVisibleIntactUsesSolarCue = refl

sunVisibleDepletionStillUsesSolarCue :
  cuePolicy sunVisibleContext macrophagesDepleted ≡ solarCueUsed
sunVisibleDepletionStillUsesSolarCue = refl

solarCueSubstitutesAcrossMacrophageState :
  cuePolicy sunVisibleContext macrophagesIntact ≡
  cuePolicy sunVisibleContext macrophagesDepleted
solarCueSubstitutesAcrossMacrophageState = refl

data CueFusionBoundary : Set where
  noTwoCueExhaustivenessClaim : CueFusionBoundary
  noFixedCuePriorityUniversality : CueFusionBoundary
  noBehavioralPolicyEqualsNeuralAlgorithmClaim : CueFusionBoundary
  noCueUseEqualsConsciousCueClaim : CueFusionBoundary
  noSolarControlErasesMagneticMechanismClaim : CueFusionBoundary

canonicalCueFusionBoundaries : List CueFusionBoundary
canonicalCueFusionBoundaries =
  noTwoCueExhaustivenessClaim
  ∷ noFixedCuePriorityUniversality
  ∷ noBehavioralPolicyEqualsNeuralAlgorithmClaim
  ∷ noCueUseEqualsConsciousCueClaim
  ∷ noSolarControlErasesMagneticMechanismClaim
  ∷ []

record AvianCueFusionReceipt : Set where
  field
    overcastDepletionEffectCarried :
      cuePolicy overcastContext macrophagesDepleted ≡ orientationDegraded

    sunnySubstitutionCarried :
      cuePolicy sunVisibleContext macrophagesIntact ≡
      cuePolicy sunVisibleContext macrophagesDepleted

    multisensoryPolicyConstrained :
      Bool
    multisensoryPolicyConstrainedIsTrue :
      multisensoryPolicyConstrained ≡ true

    fullSensorFusionRecovered :
      Bool
    fullSensorFusionRecoveredIsFalse :
      fullSensorFusionRecovered ≡ false

    consciousCueRecovered :
      Bool
    consciousCueRecoveredIsFalse :
      consciousCueRecovered ≡ false

    boundaries :
      List CueFusionBoundary

    receiptReading :
      String

canonicalAvianCueFusionReceipt : AvianCueFusionReceipt
canonicalAvianCueFusionReceipt =
  record
    { overcastDepletionEffectCarried = refl
    ; sunnySubstitutionCarried = refl
    ; multisensoryPolicyConstrained = true
    ; multisensoryPolicyConstrainedIsTrue = refl
    ; fullSensorFusionRecovered = false
    ; fullSensorFusionRecoveredIsFalse = refl
    ; consciousCueRecovered = false
    ; consciousCueRecoveredIsFalse = refl
    ; boundaries = canonicalCueFusionBoundaries
    ; receiptReading =
        "The finite witness separates a context-dependent magnetic cue from solar cue substitution; it does not claim a complete real pigeon navigation algorithm."
    }
