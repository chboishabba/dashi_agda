module DASHI.Cognition.PNF.LearningUpdateMechanismSeparationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Cognition.PNF.MemoryFibre as Memory

------------------------------------------------------------------------
-- EXTINCTION != RECONSOLIDATION != ERASURE
--
-- Literature calibration:
-- Gregory J. Quirk; Devin Mueller,
-- "Neural Mechanisms of Extinction Learning and Retrieval",
-- DOI 10.1038/sj.npp.1301555.
--
-- The finite signatures below preserve the canonical empirical distinction:
-- extinction is represented as competing/inhibitory learning with retained
-- trace; reconsolidation as retrieval-linked trace modification; erasure as
-- trace loss.  The module does not claim that every experimental protocol
-- cleanly instantiates exactly one signature.
------------------------------------------------------------------------

data MemoryUpdateMechanism : Set where
  extinctionUpdate reconsolidationUpdate erasureUpdate : MemoryUpdateMechanism

record UpdateSignature : Set where
  constructor updateSignature
  field
    originalTraceRetained : Bool
    competingInhibitionAdded : Bool
    retrievedTraceReopenedForModification : Bool

open UpdateSignature public

signature : MemoryUpdateMechanism → UpdateSignature
signature extinctionUpdate = updateSignature true true false
signature reconsolidationUpdate = updateSignature true false true
signature erasureUpdate = updateSignature false false false

extinctionIsNotErasure : extinctionUpdate ≡ erasureUpdate → ⊥
extinctionIsNotErasure ()

extinctionIsNotReconsolidation : extinctionUpdate ≡ reconsolidationUpdate → ⊥
extinctionIsNotReconsolidation ()

reconsolidationIsNotErasure : reconsolidationUpdate ≡ erasureUpdate → ⊥
reconsolidationIsNotErasure ()

extinctionAndErasureHaveDifferentRetentionSignature :
  originalTraceRetained (signature extinctionUpdate)
  ≡ originalTraceRetained (signature erasureUpdate) → ⊥
extinctionAndErasureHaveDifferentRetentionSignature ()

extinctionAndReconsolidationHaveDifferentReopeningSignature :
  retrievedTraceReopenedForModification (signature extinctionUpdate)
  ≡ retrievedTraceReopenedForModification (signature reconsolidationUpdate) → ⊥
extinctionAndReconsolidationHaveDifferentReopeningSignature ()

existingExtinctionOperationRetainsRememberedEvent :
  (memory : Memory.MemoryFibre) →
  Memory.rememberedEvent (Memory.extinguishActionDominance memory)
  ≡ Memory.rememberedEvent memory
existingExtinctionOperationRetainsRememberedEvent =
  Memory.extinctionPreservesRememberedEvent

existingExtinctionOperationSuppressesActionDominance :
  (memory : Memory.MemoryFibre) →
  Memory.actionWeight (Memory.extinguishActionDominance memory) ≡ 0
existingExtinctionOperationSuppressesActionDominance memory = refl

record LearningUpdateMechanismBoundary : Set where
  constructor learningUpdateMechanismBoundary
  field
    extinctionEqualsErasure : Bool
    extinctionEqualsReconsolidation : Bool
    reconsolidationEqualsErasure : Bool
    extinctionMayRetainOriginalTrace : Bool

canonicalLearningUpdateMechanismBoundary : LearningUpdateMechanismBoundary
canonicalLearningUpdateMechanismBoundary =
  learningUpdateMechanismBoundary false false false true
