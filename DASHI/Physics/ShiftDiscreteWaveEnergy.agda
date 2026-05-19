module DASHI.Physics.ShiftDiscreteWaveEnergy where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ; +_) renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.SchrodingerGapPhaseWaveShiftInstance as SPWSI
open import DASHI.Physics.ShiftDiscreteWaveStep as SDWS
open import DASHI.Physics.ShiftPhaseTableInterference as SPTI4
open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI

------------------------------------------------------------------------
-- Finite energy / stability surface for the Euler-style discrete-wave step.
--
-- This module stays intentionally small and finite:
--   * energy is the basis-level square norm on integer-pair waves,
--   * step energy is measured after the current Euler-style update,
--   * held-state basis waves are preserved because the local Hamiltonian
--     scale vanishes there,
--   * non-held basis waves expose explicit growth witnesses.
--
-- No unitarity, Hilbert-space, or PDE claim is made.

waveNormSq : SDWS.DiscreteWave → ℤ
waveNormSq ψ =
  (SDWS.DiscreteWave.re ψ *ℤ SDWS.DiscreteWave.re ψ)
    +ℤ
  (SDWS.DiscreteWave.im ψ *ℤ SDWS.DiscreteWave.im ψ)

basisWave : SPTI4.Phase4 → SDWS.DiscreteWave
basisWave = SDWS.encodePhase4

stepEnergy :
  SPWSI.ShiftWavePhaseState →
  SDWS.DiscreteWave →
  ℤ
stepEnergy w ψ =
  waveNormSq (SDWS.shiftSchrodingerStep4 w ψ)

basisStepEnergy :
  SPWSI.ShiftWavePhaseState →
  SPTI4.Phase4 →
  ℤ
basisStepEnergy w φ =
  stepEnergy w (basisWave φ)

startWaveState : SPWSI.ShiftWavePhaseState
startWaveState =
  SPWSI.canonicalWavePhaseState SPTI.shiftStartPoint

nextWaveState : SPWSI.ShiftWavePhaseState
nextWaveState =
  SPWSI.canonicalWavePhaseState SPTI.shiftNextPoint

heldWaveState : SPWSI.ShiftWavePhaseState
heldWaveState =
  SPWSI.canonicalWavePhaseState SPTI.shiftHeldExitPoint

basisWaveUnitEnergy :
  (φ : SPTI4.Phase4) →
  waveNormSq (basisWave φ) ≡ + 1
basisWaveUnitEnergy SPTI4.φ0 = refl
basisWaveUnitEnergy SPTI4.φ1 = refl
basisWaveUnitEnergy SPTI4.φ2 = refl
basisWaveUnitEnergy SPTI4.φ3 = refl

heldBasisStepEnergyPreserved :
  (φ : SPTI4.Phase4) →
  basisStepEnergy heldWaveState φ ≡ waveNormSq (basisWave φ)
heldBasisStepEnergyPreserved SPTI4.φ0 = refl
heldBasisStepEnergyPreserved SPTI4.φ1 = refl
heldBasisStepEnergyPreserved SPTI4.φ2 = refl
heldBasisStepEnergyPreserved SPTI4.φ3 = refl

startBasisStepEnergyWitness-φ0 :
  basisStepEnergy startWaveState SPTI4.φ0 ≡ + 17
startBasisStepEnergyWitness-φ0 = refl

nextBasisStepEnergyWitness-φ0 :
  basisStepEnergy nextWaveState SPTI4.φ0 ≡ + 2
nextBasisStepEnergyWitness-φ0 = refl

heldBasisStepEnergyWitness-φ0 :
  basisStepEnergy heldWaveState SPTI4.φ0 ≡ + 1
heldBasisStepEnergyWitness-φ0 = refl

record ShiftDiscreteWaveEnergy : Set₁ where
  field
    normSq :
      SDWS.DiscreteWave → ℤ
    basisEnergy :
      SPTI4.Phase4 → ℤ
    postStepEnergy :
      SPWSI.ShiftWavePhaseState →
      SDWS.DiscreteWave →
      ℤ
    heldBasisEnergyPreserved :
      (φ : SPTI4.Phase4) →
      postStepEnergy heldWaveState (basisWave φ)
        ≡
      normSq (basisWave φ)
    startBasisGrowthWitness :
      postStepEnergy startWaveState (basisWave SPTI4.φ0) ≡ + 17
    nextBasisGrowthWitness :
      postStepEnergy nextWaveState (basisWave SPTI4.φ0) ≡ + 2
    nonClaimBoundary : List String

shiftDiscreteWaveEnergy :
  ShiftDiscreteWaveEnergy
shiftDiscreteWaveEnergy =
  record
    { normSq = waveNormSq
    ; basisEnergy = λ φ → waveNormSq (basisWave φ)
    ; postStepEnergy = stepEnergy
    ; heldBasisEnergyPreserved = heldBasisStepEnergyPreserved
    ; startBasisGrowthWitness = startBasisStepEnergyWitness-φ0
    ; nextBasisGrowthWitness = nextBasisStepEnergyWitness-φ0
    ; nonClaimBoundary =
        "Finite discrete-wave energy package only"
        ∷ "Energy is the square norm on integer-pair basis waves"
        ∷ "Post-step energy is measured after the current Euler-style update only"
        ∷ "Held-state preservation is a local zero-Hamiltonian boundary case"
        ∷ "Non-held states expose explicit basis-level growth witnesses rather than a stability theorem"
        ∷ "No unitarity, Hilbert space, spectral theorem, or continuum PDE claim is implied"
        ∷ []
    }
