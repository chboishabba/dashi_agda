module DASHI.Cognition.PNF.MemoryCommandSeparationExact where

------------------------------------------------------------------------
-- MEMORY CONTENT != ACTION COMMAND
--
-- This module is a concrete adapter over the existing MemoryFibre.  It proves
-- that extinction changes the action projection while retaining remembered
-- EventPNF and provenance.  It does not claim that this toy operation is a
-- complete biological model of extinction/reconsolidation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)

import DASHI.Cognition.PNF.MemoryFibre as Memory

extinctionPreservesEventExact :
  ∀ memory →
  Memory.rememberedEvent (Memory.extinguishActionDominance memory) ≡
  Memory.rememberedEvent memory
extinctionPreservesEventExact = Memory.extinctionPreservesRememberedEvent

extinctionPreservesProvenanceExact :
  ∀ memory →
  Memory.memoryProvenance (Memory.extinguishActionDominance memory) ≡
  Memory.memoryProvenance memory
extinctionPreservesProvenanceExact memory = refl

extinctionZerosActionWeightExact :
  ∀ memory →
  Memory.actionWeight (Memory.extinguishActionDominance memory) ≡ zero
extinctionZerosActionWeightExact memory = refl

revaluationPreservesProvenanceExact :
  ∀ memory value →
  Memory.memoryProvenance (Memory.revalue memory value) ≡
  Memory.memoryProvenance memory
revaluationPreservesProvenanceExact memory value = refl

phaseRealignmentPreservesEventExact :
  ∀ memory newPhase →
  Memory.rememberedEvent (Memory.realignPhase memory newPhase) ≡
  Memory.rememberedEvent memory
phaseRealignmentPreservesEventExact memory newPhase = refl

phaseRealignmentPreservesProvenanceExact :
  ∀ memory newPhase →
  Memory.memoryProvenance (Memory.realignPhase memory newPhase) ≡
  Memory.memoryProvenance memory
phaseRealignmentPreservesProvenanceExact memory newPhase = refl

record MemoryCommandSeparationWitness (memory : Memory.MemoryFibre) : Set where
  constructor memoryCommandSeparationWitness
  field
    sameEvent :
      Memory.rememberedEvent (Memory.extinguishActionDominance memory) ≡
      Memory.rememberedEvent memory
    sameProvenance :
      Memory.memoryProvenance (Memory.extinguishActionDominance memory) ≡
      Memory.memoryProvenance memory
    actionProjectionIsZero :
      Memory.actionWeight (Memory.extinguishActionDominance memory) ≡ zero

open MemoryCommandSeparationWitness public

extinctionIsMemoryCommandSeparation :
  ∀ memory → MemoryCommandSeparationWitness memory
extinctionIsMemoryCommandSeparation memory =
  memoryCommandSeparationWitness
    (extinctionPreservesEventExact memory)
    (extinctionPreservesProvenanceExact memory)
    (extinctionZerosActionWeightExact memory)
