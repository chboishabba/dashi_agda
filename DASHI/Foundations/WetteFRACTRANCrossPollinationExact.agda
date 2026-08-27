module DASHI.Foundations.WetteFRACTRANCrossPollinationExact where

------------------------------------------------------------------------
-- WETTE / FRACTRAN CROSS-POLLINATION
--
-- This module demonstrates that the Wette reconstruction interface is already
-- inhabited by an existing repo-native prime-valuation machine. It is an
-- architectural witness only: Conway-style/FRACTRAN arithmetic transport is
-- not identified with Wette's historical calculus.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.FRACTRANSSPTransitionExact as F
import DASHI.Foundations.WetteConstructiveAutomatonExact as W

------------------------------------------------------------------------
-- Rule-indexed machine: each existing FRACTRAN rule is a generator.
------------------------------------------------------------------------

fractranRuleMachine : W.WetteMachineSpec
fractranRuleMachine =
  record
    { State = F.PrimeValuationState
    ; Generator = F.FRACTRANRule
    ; admissible = λ _ → true
    ; step = F.applyRule
    ; preservesAdmissible = λ _ _ _ → refl
    }

canonicalRuleTransferThroughWetteInterface :
  W.step fractranRuleMachine F.transfer47To59 F.canonicalPrimeState
  ≡ F.firstCanonicalTransfer
canonicalRuleTransferThroughWetteInterface = refl

------------------------------------------------------------------------
-- Priority machine: package the repo's first-enabled scheduler as one unary
-- generator. This is useful because Wette's later prose concerns regulated
-- effective calculation, while the mathematical content here remains simply a
-- finite deterministic transition system.
------------------------------------------------------------------------

data PriorityGenerator : Set where
  priorityStep : PriorityGenerator

priorityMachine : W.WetteMachineSpec
priorityMachine =
  record
    { State = F.PrimeValuationState
    ; Generator = PriorityGenerator
    ; admissible = λ _ → true
    ; step = λ _ → F.firstEnabledStep
    ; preservesAdmissible = λ _ _ _ → refl
    }

canonicalPriorityThroughWetteInterface :
  W.step priorityMachine priorityStep F.canonicalPrimeState
  ≡ F.firstCanonicalTransfer
canonicalPriorityThroughWetteInterface = F.canonicalPriorityUses47To59

------------------------------------------------------------------------
-- Scope boundary.
------------------------------------------------------------------------

record WetteFRACTRANCrossPollinationScope : Set where
  constructor wetteFRACTRANCrossPollinationScope
  field
    existingPrimeValuationMachineFitsInterface : Bool
    existingPrimeValuationMachineFitsInterfaceIsTrue :
      existingPrimeValuationMachineFitsInterface ≡ true

    existingPriorityMachineFitsInterface : Bool
    existingPriorityMachineFitsInterfaceIsTrue :
      existingPriorityMachineFitsInterface ≡ true

    fractranMachineIsHistoricalWetteMachine : Bool
    fractranMachineIsHistoricalWetteMachineIsFalse :
      fractranMachineIsHistoricalWetteMachine ≡ false

    finitePriorityWitnessProvesWetteConsistency : Bool
    finitePriorityWitnessProvesWetteConsistencyIsFalse :
      finitePriorityWitnessProvesWetteConsistency ≡ false

canonicalWetteFRACTRANCrossPollinationScope :
  WetteFRACTRANCrossPollinationScope
canonicalWetteFRACTRANCrossPollinationScope =
  wetteFRACTRANCrossPollinationScope
    true refl
    true refl
    false refl
    false refl
