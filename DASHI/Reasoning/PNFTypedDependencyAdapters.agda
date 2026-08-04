module DASHI.Reasoning.PNFTypedDependencyAdapters where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Reasoning.PNFZizekOperator as Zizek
import DASHI.Reasoning.TypedHyperfabricCore as Hyperfabric

------------------------------------------------------------------------
-- Concrete adapters from legacy Boolean projections to proof-bearing types.
--
-- The memory adapter reuses existing in-repo preservation theorems.  The
-- closure adapter requires an actual compatible global section rather than a
-- closure narrative or a bare availability flag.
------------------------------------------------------------------------

data MemoryUpdate : Set where
  revaluationUpdate : Nat → MemoryUpdate
  habituationUpdate : MemoryUpdate
  inhibitoryExtinctionUpdate : MemoryUpdate

applyMemoryUpdate : MemoryUpdate → Memory.MemoryFibre → Memory.MemoryFibre
applyMemoryUpdate (revaluationUpdate value) memory = Memory.revalue memory value
applyMemoryUpdate habituationUpdate memory = Memory.habituate memory
applyMemoryUpdate inhibitoryExtinctionUpdate memory =
  Memory.extinguishActionDominance memory

MemoryEventPreserved :
  MemoryUpdate → Memory.MemoryFibre → Set
MemoryEventPreserved update memory =
  Memory.rememberedEvent (applyMemoryUpdate update memory)
  ≡ Memory.rememberedEvent memory

memoryUpdatePreservesEvent :
  ∀ update memory → MemoryEventPreserved update memory
memoryUpdatePreservesEvent (revaluationUpdate value) memory =
  Memory.revaluePreservesRememberedEvent memory value
memoryUpdatePreservesEvent habituationUpdate memory =
  Memory.habituationPreservesRememberedEvent memory
memoryUpdatePreservesEvent inhibitoryExtinctionUpdate memory =
  Memory.extinctionPreservesRememberedEvent memory

record TypedClosureGluing
    {Vertex Edge : Set}
    (closure : Zizek.PNFIdeologicalClosure) : Set₁ where
  field
    fabric : Hyperfabric.TypedHyperfabric Vertex Edge
    globalSection : Hyperfabric.GlobalSection fabric
    availabilityProjection :
      Zizek.PNFIdeologicalClosure.actualGluingWitnessAvailable closure
      ≡ true
    closureToFabricReceipt : String

open TypedClosureGluing public

closureGluingProjectsAvailable :
  ∀ {Vertex Edge : Set}
    {closure : Zizek.PNFIdeologicalClosure} →
  TypedClosureGluing {Vertex} {Edge} closure →
  Zizek.PNFIdeologicalClosure.actualGluingWitnessAvailable closure ≡ true
closureGluingProjectsAvailable witness = availabilityProjection witness

record PNFDependencyAdapterBoundary : Set where
  field
    memoryPreservationUsesExistingProofs : Bool
    closureGluingRequiresGlobalSection : Bool
    closureNarrativeAloneCreatesSection : Bool
    availabilityBooleanReconstructsSection : Bool
    allLearningModesPreserveRememberedEvent : Bool
    boundaryNote : String

canonicalPNFDependencyAdapterBoundary : PNFDependencyAdapterBoundary
canonicalPNFDependencyAdapterBoundary = record
  { memoryPreservationUsesExistingProofs = true
  ; closureGluingRequiresGlobalSection = true
  ; closureNarrativeAloneCreatesSection = false
  ; availabilityBooleanReconstructsSection = false
  ; allLearningModesPreserveRememberedEvent = false
  ; boundaryNote =
      "Revaluation, habituation and inhibitory extinction reuse exact remembered-event preservation theorems. Other update modes need their own indexed evidence; a gluing flag cannot reconstruct a section."
  }
