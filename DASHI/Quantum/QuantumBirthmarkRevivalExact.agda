{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkRevivalExact where

open import Agda.Builtin.Bool using (Bool; true; false)

------------------------------------------------------------------------
-- REVIVAL-ENHANCED QUANTUM BIRTHMARK
--
-- The paper decomposes the long-time enhancement into a universal RMT part
-- and a short-time-dynamics correction.  Early recurrences prior to the
-- Heisenberg time constrain the spectral envelope and reduce effective phase-
-- space exploration.  Scars are one important cause, but not the definition.
------------------------------------------------------------------------

record RevivalCorrectionModel : Set₁ where
  field
    State : Set
    Time : Set
    Fidelity : Set
    Factor : Set

    heisenbergTime : Time
    CutoffTime : Set
    cutoff : CutoffTime
    EarlierThan : Time → Time → Set

    fidelity : State → Time → Fidelity
    rmtBaseline : State → Time → Fidelity
    revivalFactor : State → Factor
    universalFactor : State → Factor
    revivalCorrectedBirthmark : State → Factor

    EarlyRecurrence : State → Time → Set
    revivalBeforeHeisenberg :
      (state : State) (time : Time) →
      EarlyRecurrence state time →
      EarlierThan time heisenbergTime →
      Set

    shortTimeCorrectionReceipt : State → Set
    multiplicativeDecompositionReceipt : State → Set

record RevivalClaimBoundary : Set where
  field
    earlyRecurrenceCanIncreaseLongTimeMemory : Bool
    revivalCorrectionComparedAgainstRMTBaseline : Bool
    scarNotRequiredForRevival : Bool
    periodicOrbitNotRequiredForRevival : Bool
    wallOrPotentialReturnCanContribute : Bool
    fullRevivalAfterHeisenbergIsDifferentRegime : Bool
    cutoffChoiceIsSystemDependent : Bool

revivalClaimBoundary : RevivalClaimBoundary
revivalClaimBoundary = record
  { earlyRecurrenceCanIncreaseLongTimeMemory = true
  ; revivalCorrectionComparedAgainstRMTBaseline = true
  ; scarNotRequiredForRevival = true
  ; periodicOrbitNotRequiredForRevival = true
  ; wallOrPotentialReturnCanContribute = true
  ; fullRevivalAfterHeisenbergIsDifferentRegime = true
  ; cutoffChoiceIsSystemDependent = true
  }

record RevivalPromotionFirewall : Set where
  field
    revivalDoesNotEqualScar : Bool
    earlyRecurrenceDoesNotImplyExactPeriodicEvolution : Bool
    sourceFormulaDoesNotSupplyUniversalCutoff : Bool

revivalPromotionFirewall : RevivalPromotionFirewall
revivalPromotionFirewall = record
  { revivalDoesNotEqualScar = true
  ; earlyRecurrenceDoesNotImplyExactPeriodicEvolution = true
  ; sourceFormulaDoesNotSupplyUniversalCutoff = true
  }
