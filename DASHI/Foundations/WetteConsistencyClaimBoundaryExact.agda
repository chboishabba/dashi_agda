module DASHI.Foundations.WetteConsistencyClaimBoundaryExact where

------------------------------------------------------------------------
-- EDUARD WETTE / PAUL BERNAYS SOURCE CONTEXT
--
-- Eduard Wette,
-- "Contradiction within pure number theory because of a system-internal
-- 'consistency'-deduction", International Logic Review 5, no. 9 (1974),
-- 51--62.
--
-- Paul Bernays,
-- "Zum Symposium ueber die Grundlagen der Mathematik",
-- Dialectica 25 (1971), 171--195.
-- DOI: 10.1111/j.1746-8361.1971.tb00598.x.
--
-- G. Kreisel and J. Zucker reviewed Wette's 1969 constructive-arithmetic
-- chapter in Journal of Symbolic Logic 37 (1972), 203--204.
-- DOI: 10.2307/2272630.
--
-- Earlier constructive-arithmetic work is treated separately from this later
-- metamathematical claim. No DOI is asserted for the 1974 Wette paper until a
-- stable bibliographic record is independently verified.
--
-- DASHI CONTRIBUTION
--
-- Make the promotion boundaries explicit. A representation, executable
-- machine, simulation theorem, proof translation, representation/kernel
-- commuting theorem, or conditional consistency-to-contradiction reduction is
-- not definitionally a soundness theorem, an actual internal consistency proof,
-- or a contradiction in ordinary arithmetic.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

import DASHI.Automata.KernelInternal as KI
import DASHI.Physics.Foundations.FormalReceiptBoundaryExact as Receipt
import DASHI.Physics.Closure.RepresentationKernelCompatibility as R
import DASHI.Foundations.WetteArithmeticRepresentationExact as Representation
import DASHI.Foundations.WetteConstructiveAutomatonExact as Automaton
import DASHI.Foundations.WetteRepresentationKernelBridgeExact as KernelBridge
import DASHI.Foundations.WetteFiniteCalculusTranslationExact as Translation
import DASHI.Foundations.WetteBernaysConsistencyDeductionBoundaryExact as Bernays

data WetteClaimLevel : Set where
  arithmeticRepresentation : WetteClaimLevel
  executableMachine : WetteClaimLevel
  deductionSimulation : WetteClaimLevel
  finiteProofTranslation : WetteClaimLevel
  finiteEquiconsistency : WetteClaimLevel
  conditionalConsistencyReduction : WetteClaimLevel
  arithmeticSoundness : WetteClaimLevel
  internalConsistency : WetteClaimLevel
  classicalContradiction : WetteClaimLevel

record WetteClaimBoundary : Set₁ where
  constructor wetteClaimBoundary
  field
    receiptBoundary : Receipt.FormalReceiptBoundary
    bernaysBoundary : Bernays.WetteBernaysBoundary
    translationBoundary : Translation.WetteTranslationBoundary

    representationAvailable : Bool
    representationAvailableIsTrue :
      representationAvailable ≡ true

    genericKernelMachineAvailable : Bool
    genericKernelMachineAvailableIsTrue :
      genericKernelMachineAvailable ≡ true

    simulationInterfaceAvailable : Bool
    simulationInterfaceAvailableIsTrue :
      simulationInterfaceAvailable ≡ true

    finiteProofTranslationInterfaceAvailable : Bool
    finiteProofTranslationInterfaceAvailableIsTrue :
      finiteProofTranslationInterfaceAvailable ≡ true

    representationKernelOwnerAvailable : Bool
    representationKernelOwnerAvailableIsTrue :
      representationKernelOwnerAvailable ≡ true

    conditionalConsistencyReductionAvailable : Bool
    conditionalConsistencyReductionAvailableIsTrue :
      conditionalConsistencyReductionAvailable ≡ true

    historicalRuleSetRecovered : Bool
    historicalRuleSetRecoveredIsFalse :
      historicalRuleSetRecovered ≡ false

    historicalWetteOrdinaryArithmeticEquiconsistencyRecovered : Bool
    historicalWetteOrdinaryArithmeticEquiconsistencyRecoveredIsFalse :
      historicalWetteOrdinaryArithmeticEquiconsistencyRecovered ≡ false

    wetteInternalConsistencyProofRecovered : Bool
    wetteInternalConsistencyProofRecoveredIsFalse :
      wetteInternalConsistencyProofRecovered ≡ false

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
    Bernays.canonicalWetteBernaysBoundary
    Translation.canonicalWetteTranslationBoundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
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

proofTranslationInterfaceDoesNotSupplyHistoricalEquiconsistency :
  finiteProofTranslationInterfaceAvailable canonicalWetteClaimBoundary ≡ true
  × historicalWetteOrdinaryArithmeticEquiconsistencyRecovered
      canonicalWetteClaimBoundary ≡ false
proofTranslationInterfaceDoesNotSupplyHistoricalEquiconsistency = refl , refl

conditionalReductionDoesNotSupplyInternalProof :
  conditionalConsistencyReductionAvailable canonicalWetteClaimBoundary ≡ true
  × wetteInternalConsistencyProofRecovered canonicalWetteClaimBoundary ≡ false
conditionalReductionDoesNotSupplyInternalProof = refl , refl

conditionalReductionDoesNotSetContradictionFlag :
  conditionalConsistencyReductionAvailable canonicalWetteClaimBoundary ≡ true
  × contradictionInOrdinaryArithmeticProved canonicalWetteClaimBoundary ≡ false
conditionalReductionDoesNotSetContradictionFlag = refl , refl

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

translationBoundaryOwner : Translation.WetteTranslationBoundary
translationBoundaryOwner = Translation.canonicalWetteTranslationBoundary

bernaysConditionalOwner : Bernays.WetteBernaysBoundary
bernaysConditionalOwner = Bernays.canonicalWetteBernaysBoundary
