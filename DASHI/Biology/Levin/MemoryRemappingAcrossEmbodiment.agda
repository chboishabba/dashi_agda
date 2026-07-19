module DASHI.Biology.Levin.MemoryRemappingAcrossEmbodiment where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Memory persistence and memory usability are distinct.  A retained trace
-- may require a decoder adapted to new neural, somatic, or sensorimotor
-- architecture before it can guide behaviour.

record MemoryRemappingWitness : Set where
  field
    tracePersistsAcrossReplacement : Bool
    oldDecoderUnavailable : Bool
    newDecoderConstructed : Bool
    behaviourallyAccessibleAfterRemap : Bool
    persistenceNotLocationProof : Bool
    remappingNotPersonalIdentityProof : Bool
    candidateOnly : Bool
    reading : String

open MemoryRemappingWitness public

canonicalMemoryRemappingWitness : MemoryRemappingWitness
canonicalMemoryRemappingWitness = record
  { tracePersistsAcrossReplacement = true
  ; oldDecoderUnavailable = true
  ; newDecoderConstructed = true
  ; behaviourallyAccessibleAfterRemap = true
  ; persistenceNotLocationProof = false
  ; remappingNotPersonalIdentityProof = false
  ; candidateOnly = true
  ; reading =
      "A memory trace may survive loss or replacement of its former implementation and become behaviourally available through a new decoder; this witnesses remapping without proving a unique storage location or continuity of personal identity"
  }

canonicalPersistenceNotLocationProof :
  persistenceNotLocationProof canonicalMemoryRemappingWitness ≡ false
canonicalPersistenceNotLocationProof = refl

record RegeneratedTissueAccessBoundary : Set where
  field
    oldTissueFormedTrace : Bool
    oldTissueRemoved : Bool
    newTissueAccessesTrace : Bool
    accessRequiresInterventionSensitiveEvidence : Bool
    noNonphysicalCarrierPromotion : Bool

open RegeneratedTissueAccessBoundary public

canonicalRegeneratedTissueAccessBoundary : RegeneratedTissueAccessBoundary
canonicalRegeneratedTissueAccessBoundary = record
  { oldTissueFormedTrace = true
  ; oldTissueRemoved = true
  ; newTissueAccessesTrace = true
  ; accessRequiresInterventionSensitiveEvidence = true
  ; noNonphysicalCarrierPromotion = false
  }
