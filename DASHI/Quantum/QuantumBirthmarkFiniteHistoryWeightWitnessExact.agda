{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkFiniteHistoryWeightWitnessExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.FiniteHistoryFunctionalExact as History
import DASHI.Quantum.QuantumBirthmarkHistoryWeightSelectionExact as Weight

------------------------------------------------------------------------
-- FINITE MICROSCOPIC WEIGHTING WITNESS
--
-- The future-boundary label is used only as a finite context/birthmark carrier.
-- Its context-conditioned weight selects the action of the corresponding
-- already-admissible finite history.  This proves inhabitance of the abstract
-- weighting interface without claiming that this toy law is the cosmological
-- quantum birthmark law.
------------------------------------------------------------------------

Admissible : History.History3 → Set
Admissible history =
  History.classifyHistory history ≡ History.admissibleHistory

contextWeight : History.FinalBoundary → History.History3 → Nat
contextWeight History.finalB history =
  History.historyAction History.historyACB
contextWeight History.finalC history =
  History.historyAction History.historyABC

finiteBirthmarkWeightSelection : Weight.BirthmarkHistoryWeightSelection
finiteBirthmarkWeightSelection = record
  { Weight.BirthmarkHistoryWeightSelection.BirthmarkRecord = History.FinalBoundary
  ; Weight.BirthmarkHistoryWeightSelection.History = History.History3
  ; Weight.BirthmarkHistoryWeightSelection.Weight = Nat
  ; Weight.BirthmarkHistoryWeightSelection.admissibleHistory = Admissible
  ; Weight.BirthmarkHistoryWeightSelection.historyWeight = contextWeight
  ; Weight.BirthmarkHistoryWeightSelection.selectedBirthmark = History.finalC
  ; Weight.BirthmarkHistoryWeightSelection.selectedHistory = History.historyABC
  ; Weight.BirthmarkHistoryWeightSelection.selectedHistoryAdmissible = refl
  }

historyABCWeight :
  contextWeight History.finalC History.historyABC ≡ 2
historyABCWeight = refl

historyACBWeight :
  contextWeight History.finalB History.historyACB ≡ 4
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
