{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkFiniteHistoryWeightWitnessExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.FiniteHistoryFunctionalExact as History
import DASHI.Quantum.QuantumBirthmarkHistoryWeightSelectionExact as Weight

Admissible : History.History3 → Set
Admissible history =
  History.classifyHistory history ≡ History.admissibleHistory

contextWeight : History.FinalBoundary → History.History3 → Nat
contextWeight History.finalB history = History.historyAction History.historyACB
contextWeight History.finalC history = History.historyAction History.historyABC

finiteBirthmarkWeightSelection : Weight.BirthmarkHistoryWeightSelection
finiteBirthmarkWeightSelection = record
  { BirthmarkRecord = History.FinalBoundary
  ; History = History.History3
  ; Weight = Nat
  ; admissibleHistory = Admissible
  ; historyWeight = contextWeight
  ; selectedBirthmark = History.finalC
  ; selectedHistory = History.historyABC
  ; selectedHistoryAdmissible = refl
  }
  where open Weight.BirthmarkHistoryWeightSelection

historyABCWeight : contextWeight History.finalC History.historyABC ≡ 2
historyABCWeight = refl

historyACBWeight : contextWeight History.finalB History.historyACB ≡ 4
historyACBWeight = refl

contextCanChangeFiniteWeight :
  contextWeight History.finalC History.historyABC ≡ 2
  × contextWeight History.finalB History.historyABC ≡ 4
contextCanChangeFiniteWeight = refl , refl

finiteMicroscopicWeightWitnessOwned : Bool
finiteMicroscopicWeightWitnessOwned = true

normalizationRuleDerivedInFiniteWitness : Bool
normalizationRuleDerivedInFiniteWitness = false

quantumAmplitudeRuleDerivedInFiniteWitness : Bool
quantumAmplitudeRuleDerivedInFiniteWitness = false

finiteWitnessIsNotContinuumLaw : Bool
finiteWitnessIsNotContinuumLaw = true

cosmologicalBirthmarkWeightLawDerived : Bool
cosmologicalBirthmarkWeightLawDerived = false
