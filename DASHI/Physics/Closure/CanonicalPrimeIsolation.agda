module DASHI.Physics.Closure.CanonicalPrimeIsolation where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (zero; suc)

open import DASHI.Execution.Contract as EC
open import DASHI.Geometry.ShiftLorentzEmergenceInstance as SLEI
open import DASHI.Physics.Closure.CanonicalPrimeSelectionBridge
  using (ShiftContractState; shiftStep)
open import DASHI.Physics.Closure.CanonicalPrimeConcentration
  using (PrimeConcentrated)
open import DASHI.Physics.Closure.CanonicalPrimeSelector
  using
    ( selectPrime
    ; selector-sound
    ; selector-no-loss-target
    ; selector-step-coarse-target
    )
open import DASHI.Physics.Closure.ShiftRGObservableInstance
  using (shiftCoarse)
open import MonsterOntos using (SSP)

private
  ShiftC : EC.Contract
  ShiftC = SLEI.shiftContract {suc zero} {suc (suc (suc zero))}

record CanonicalPrimeIsolation : Set₁ where
  field
    selectedPrime : ShiftContractState → SSP
    selectedPrimeAtIsConcentrated :
      ∀ x →
      PrimeConcentrated x (selectedPrime x)
    selectedPrimeNoLoss :
      EC.Contract.ExecutionAdmissible ShiftC
        →
      ∀ x →
      PrimeConcentrated (shiftStep x) (selectedPrime (shiftStep x))
        →
      PrimeConcentrated x (selectedPrime x)
    selectedPrimeStepCoarse :
      ∀ x →
      selectedPrime (shiftCoarse (shiftStep x))
        ≡
      selectedPrime (shiftStep (shiftCoarse x))

canonicalPrimeIsolation : CanonicalPrimeIsolation
canonicalPrimeIsolation = record
  { selectedPrime = selectPrime
  ; selectedPrimeAtIsConcentrated = selector-sound
  ; selectedPrimeNoLoss = selector-no-loss-target
  ; selectedPrimeStepCoarse = selector-step-coarse-target
  }
