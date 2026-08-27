module DASHI.Cognition.PNF.PNFFastAccessMemoryLearningBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List)

import DASHI.Cognition.PNF.FastAccessControlFieldExact as Access
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PNF.LearningAlgebra as Learning
import DASHI.Cognition.PNF.FibreLearningDynamics as FibreLearning
import DASHI.Cognition.PNF.BraidLearningTransport as Braid
import DASHI.Interop.SensibLawResidualLattice as Residual

------------------------------------------------------------------------
-- PNF owns semantic revision.  Fast access owns momentary availability.
-- This bridge connects those existing owners without identifying them.
------------------------------------------------------------------------

record MemoryAccessSnapshot : Set where
  constructor memoryAccessSnapshot
  field
    memory : Memory.MemoryFibre
    accessible : Bool

open MemoryAccessSnapshot public

record SameMemoryDifferentAccess : Set where
  constructor sameMemoryDifferentAccess
  field
    retained : Memory.MemoryFibre
    first second : MemoryAccessSnapshot
    firstMemory-v : memory first ≡ retained
    secondMemory-v : memory second ≡ retained
    firstAccessible : accessible first ≡ false
    secondAccessible : accessible second ≡ true

sameMemoryCanChangeAccess :
  (m : Memory.MemoryFibre) →
  SameMemoryDifferentAccess
sameMemoryCanChangeAccess m =
  sameMemoryDifferentAccess
    m
    (memoryAccessSnapshot m false)
    (memoryAccessSnapshot m true)
    refl refl refl refl

sameMemoryMeansSameRememberedPNF :
  (m : Memory.MemoryFibre) →
  Memory.rememberedEvent
    (memory (first (sameMemoryCanChangeAccess m)))
  ≡
  Memory.rememberedEvent
    (memory (second (sameMemoryCanChangeAccess m)))
sameMemoryMeansSameRememberedPNF m = refl

------------------------------------------------------------------------
-- Existing learning operations already carry the right anti-erasure laws.
------------------------------------------------------------------------

phaseRealignmentPreservesRememberedPNF :
  (m : Memory.MemoryFibre) →
  (newPhase : Nat) →
  Memory.rememberedEvent (Memory.realignPhase m newPhase)
  ≡ Memory.rememberedEvent m
phaseRealignmentPreservesRememberedPNF m newPhase = refl

phaseRealignmentActuallySetsPhase :
  (m : Memory.MemoryFibre) →
  (newPhase : Nat) →
  Memory.phase (Memory.realignPhase m newPhase) ≡ newPhase
phaseRealignmentActuallySetsPhase m newPhase = refl

extinctionPreservesRememberedPNF :
  (m : Memory.MemoryFibre) →
  Memory.rememberedEvent (Memory.extinguishActionDominance m)
  ≡ Memory.rememberedEvent m
extinctionPreservesRememberedPNF =
  Memory.extinctionPreservesRememberedEvent

extinctionZerosActionWeight :
  (m : Memory.MemoryFibre) →
  Memory.actionWeight (Memory.extinguishActionDominance m) ≡ zero
extinctionZerosActionWeight m = refl

phaseReceiptUsesExistingLearningKind :
  (m : Memory.MemoryFibre) →
  (newPhase : Nat) →
  Learning.learningKind (Learning.phaseRealignmentReceipt m newPhase)
  ≡ Learning.phaseRealignmentLearning
phaseReceiptUsesExistingLearningKind m newPhase = refl

extinctionReceiptUsesExistingLearningKind :
  (m : Memory.MemoryFibre) →
  Learning.learningKind (Learning.extinctionReceipt m)
  ≡ Learning.extinctionLearning
extinctionReceiptUsesExistingLearningKind m = refl

------------------------------------------------------------------------
-- Formal NO_TYPED_MEET and transient access failure are distinct layers.
-- The finite countermodel below makes an access-blocked state inhabit an exact
-- formal residual.  Therefore no rule may infer NO_TYPED_MEET from access
-- failure alone.
------------------------------------------------------------------------

data AccessFormalState : Set where
  blockedButFormallyExact accessibleAndPartial : AccessFormalState

accessSurface : AccessFormalState → Bool
accessSurface blockedButFormallyExact = false
accessSurface accessibleAndPartial = true

formalResidual : AccessFormalState → Residual.ResidualLevel
formalResidual blockedButFormallyExact = Residual.exact
formalResidual accessibleAndPartial = Residual.partial

exactNotNoTypedMeet : Residual.exact ≡ Residual.noTypedMeet → ⊥
exactNotNoTypedMeet ()

partialNotExact : Residual.partial ≡ Residual.exact → ⊥
partialNotExact ()

accessFailureCannotForceNoTypedMeet :
  ((s : AccessFormalState) →
    accessSurface s ≡ false →
    formalResidual s ≡ Residual.noTypedMeet) →
  ⊥
accessFailureCannotForceNoTypedMeet rule =
  exactNotNoTypedMeet (rule blockedButFormallyExact refl)

accessSuccessCannotForceFormalExactness :
  ((s : AccessFormalState) →
    accessSurface s ≡ true →
    formalResidual s ≡ Residual.exact) →
  ⊥
accessSuccessCannotForceFormalExactness rule =
  partialNotExact (rule accessibleAndPartial refl)

------------------------------------------------------------------------
-- Existing within-fibre rewiring is the slow-learning analogue: public PNF and
-- remembered event may remain fixed while transition topology changes.
------------------------------------------------------------------------

existingRewirePreservesRememberedPNF :
  (m : Memory.MemoryFibre) →
  (label : String) →
  (oldGraph newGraph : List Learning.WeightedTransition) →
  Memory.rememberedEvent
    (FibreLearning.after
      (FibreLearning.rewireWithinFibre m label oldGraph newGraph))
  ≡ Memory.rememberedEvent m
existingRewirePreservesRememberedPNF m label oldGraph newGraph = refl

record AccessLearningLayerBoundary : Set where
  constructor accessLearningLayerBoundary
  field
    accessChangeIsPNFRevision : Bool
    noTypedMeetIsAccessFailure : Bool
    extinctionErasesRememberedEvent : Bool
    phaseRealignmentChangesRememberedEvent : Bool
    braidResidualIsAutomaticallyNeuralWaveCause : Bool

canonicalAccessLearningLayerBoundary : AccessLearningLayerBoundary
canonicalAccessLearningLayerBoundary =
  accessLearningLayerBoundary false false false false false
