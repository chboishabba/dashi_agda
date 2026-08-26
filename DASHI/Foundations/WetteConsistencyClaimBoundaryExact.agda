module DASHI.Foundations.WetteConsistencyClaimBoundaryExact where

------------------------------------------------------------------------
-- EDUARD WETTE SOURCE CONTEXT
--
-- Eduard Wette,
-- "Contradiction within pure number theory because of a system-internal
-- 'consistency'-deduction", International Logic Review (1974), 51--62.
--
-- Earlier constructive-arithmetic work is treated separately from this later
-- metamathematical claim. No DOI is asserted until independently verified.
--
-- DASHI CONTRIBUTION
--
-- Make the promotion boundaries explicit. A representation, executable
-- machine, simulation theorem, or representation/kernel commuting theorem is
-- not definitionally a soundness theorem, an internal consistency theorem, or
-- a contradiction in ordinary arithmetic.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Automata.KernelInternal as KI
import DASHI.Physics.Foundations.FormalReceiptBoundaryExact as Receipt
import DASHI.Physics.Closure.RepresentationKernelCompatibility as R
import DASHI.Foundations.WetteArithmeticRepresentationExact as Representation
import DASHI.Foundations.WetteConstructiveAutomatonExact as Automaton
import DASHI.Foundations.WetteRepresentationKernelBridgeExact as KernelBridge

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

    representationKernelOwnerAvailable : Bool
    representationKernelOwnerAvailableIsTrue :
      representationKernelOwnerAvailable ≡ true

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
    true refl
    false refl
    false refl
    false refl
    false refl

representationDoesNotSetConsistencyFlag :
  systemInternalConsistencyProved canonicalWetteClaimBoundary ≡ false
representationDoesNotSetConsistencyFlag = refl

representationKernelDoesNotSetConsistencyFlag :
  representationKernelOwnerAvailable canonicalWetteClaimBoundary ≡ true
  × systemInternalConsistencyProved canonicalWetteClaimBoundary ≡ false
representationKernelDoesNotSetConsistencyFlag = refl , refl

simulationInterfaceDoesNotSetContradictionFlag :
  contradictionInOrdinaryArithmeticProved canonicalWetteClaimBoundary ≡ false
simulationInterfaceDoesNotSetContradictionFlag = refl

historicalRecoveryStillRequired :
  historicalRuleSetRecovered canonicalWetteClaimBoundary ≡ false
historicalRecoveryStillRequired = refl

representationOwner : Representation.WetteArithmeticRepresentation
representationOwner = Representation.canonicalWetteArithmeticRepresentation

automatonOwner :
  (machine : Automaton.WetteMachineSpec) → KI.KernelInternalAutomaton
automatonOwner = Automaton.asKernelInternalAutomaton

representationKernelOwner :
  {machine : Automaton.WetteMachineSpec} →
  (simulation : Automaton.WetteDeductionSimulation machine) →
  (g : Automaton.Generator machine) →
  R.RepresentationKernelCompatibility
representationKernelOwner = KernelBridge.fixedGeneratorCompatibility
