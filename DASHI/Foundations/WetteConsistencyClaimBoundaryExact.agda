{-# OPTIONS --safe #-}
module DASHI.Foundations.WetteConsistencyClaimBoundaryExact where

------------------------------------------------------------------------
-- EDUARD WETTE SOURCE CONTEXT
--
-- Eduard Wette,
-- "Contradiction within pure number theory because of a system-internal
-- 'consistency'-deduction", International Logic Review (1974), 51--62.
--
-- Earlier constructive-arithmetic work is treated separately from this later
-- metamathematical claim.  No DOI is asserted until independently verified.
--
-- DASHI CONTRIBUTION
--
-- Make the promotion boundaries explicit.  A representation, executable
-- machine, or simulation theorem is not definitionally a soundness theorem,
-- an internal consistency theorem, or a contradiction in ordinary arithmetic.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.FormalReceiptBoundaryExact as Receipt
import DASHI.Foundations.WetteArithmeticRepresentationExact as Representation
import DASHI.Foundations.WetteConstructiveAutomatonExact as Automaton

data WetteClaimLevel : Set where
  arithmeticRepresentation : WetteClaimLevel
  executableMachine : WetteClaimLevel
  deductionSimulation : WetteClaimLevel
  arithmeticSoundness : WetteClaimLevel
  internalConsistency : WetteClaimLevel
  classicalContradiction : WetteClaimLevel

record WetteClaimBoundary : Set₁ where
  constructor wetteClaimBoundary
  field
    receiptBoundary : Receipt.FormalReceiptBoundary

    representationAvailable : Bool
    representationAvailableIsTrue :
      representationAvailable ≡ true

    genericKernelMachineAvailable : Bool
    genericKernelMachineAvailableIsTrue :
      genericKernelMachineAvailable ≡ true

    simulationInterfaceAvailable : Bool
    simulationInterfaceAvailableIsTrue :
      simulationInterfaceAvailable ≡ true

    historicalRuleSetRecovered : Bool
    historicalRuleSetRecoveredIsFalse :
      historicalRuleSetRecovered ≡ false

    arithmeticSoundnessProved : Bool
    arithmeticSoundnessProvedIsFalse :
      arithmeticSoundnessProved ≡ false

    systemInternalConsistencyProved : Bool
    systemInternalConsistencyProvedIsFalse :
      systemInternalConsistencyProved ≡ false

    contradictionInOrdinaryArithmeticProved : Bool
    contradictionInOrdinaryArithmeticProvedIsFalse :
      contradictionInOrdinaryArithmeticProved ≡ false

open WetteClaimBoundary public

canonicalWetteClaimBoundary : WetteClaimBoundary
canonicalWetteClaimBoundary =
  wetteClaimBoundary
    Receipt.canonicalFormalReceiptBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Concrete separation witnesses: the canonical reconstruction state carries
-- positive representation/interface facts while the stronger claims remain
-- explicitly false.  This prevents accidental prose-level promotion.
------------------------------------------------------------------------

representationDoesNotSetConsistencyFlag :
  systemInternalConsistencyProved canonicalWetteClaimBoundary ≡ false
representationDoesNotSetConsistencyFlag = refl

simulationInterfaceDoesNotSetContradictionFlag :
  contradictionInOrdinaryArithmeticProved canonicalWetteClaimBoundary ≡ false
simulationInterfaceDoesNotSetContradictionFlag = refl

historicalRecoveryStillRequired :
  historicalRuleSetRecovered canonicalWetteClaimBoundary ≡ false
historicalRecoveryStillRequired = refl

------------------------------------------------------------------------
-- Imported owners are intentionally referenced here so this boundary remains
-- attached to the actual reusable machinery rather than becoming a parallel
-- standalone vocabulary.
------------------------------------------------------------------------

representationOwner : Representation.WetteArithmeticRepresentation
representationOwner = Representation.canonicalWetteArithmeticRepresentation

automatonOwner :
  (machine : Automaton.WetteMachineSpec) →
  DASHI.Automata.KernelInternal.KernelInternalAutomaton
automatonOwner = Automaton.asKernelInternalAutomaton
