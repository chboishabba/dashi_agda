module DASHI.Cognition.CaveTraumaNonErasingReopeningExact where

------------------------------------------------------------------------
-- NON-ERASING CORRECTIVE REOPENING
--
-- A finite structural recovery witness over existing DASHI carriers.
--
-- Corrective evidence:
--
--   contracted accessible subfabric
--        ->
--   reopened accessible subfabric
--
-- while an extinction-style memory update preserves the remembered event and
-- provenance but changes current action dominance.
--
-- This is NOT a clinical theorem about trauma treatment.  It establishes only
-- that the repo can represent recovery/refinement without memory erasure.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AdmissibleReachability as AdmissibleReach
import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Biology.ObserverRelativeReachableSubfabricExact as Reach
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PNF.MemoryCommandSeparationExact as MemoryCommand

record RecoveryState : Set where
  constructor recovery-state
  field
    memory : Memory.MemoryFibre
    accessible : Reach.AccessibleSupervoxel

open RecoveryState public

beforeRecovery : Memory.MemoryFibre → RecoveryState
beforeRecovery memory =
  recovery-state memory Reach.contractedAccessible

afterRecovery : Memory.MemoryFibre → RecoveryState
afterRecovery memory =
  recovery-state
    (Memory.extinguishActionDominance memory)
    Reach.reopenedAccessible

data RecoveryAction : Set where
  correctiveEvidence : RecoveryAction

data RecoveryPrecondition : RecoveryState → RecoveryAction → Set where
  correctiveEvidenceAvailable :
    (memory : Memory.MemoryFibre) →
    RecoveryPrecondition
      (beforeRecovery memory)
      correctiveEvidence

data RecoveryPostcondition :
    RecoveryState → RecoveryAction → RecoveryState → Set where
  correctiveEvidenceReopens :
    (memory : Memory.MemoryFibre) →
    RecoveryPostcondition
      (beforeRecovery memory)
      correctiveEvidence
      (afterRecovery memory)

recoveryActionLabel : RecoveryAction → String
recoveryActionLabel correctiveEvidence =
  "corrective-evidence-reopening"

recoverySystem :
  Dependency.DependentActionSystem RecoveryState RecoveryAction
recoverySystem = record
  { Dependency.Precondition = RecoveryPrecondition
  ; Dependency.Postcondition = RecoveryPostcondition
  ; Dependency.actionLabel = recoveryActionLabel
  }

canonicalCorrectiveAction :
  (memory : Memory.MemoryFibre) →
  Dependency.AdmissibleAction
    recoverySystem
    (beforeRecovery memory)
    correctiveEvidence
canonicalCorrectiveAction memory = record
  { Dependency.precondition =
      correctiveEvidenceAvailable memory
  ; Dependency.after =
      afterRecovery memory
  ; Dependency.postcondition =
      correctiveEvidenceReopens memory
  ; Dependency.dependencyReceipt =
      "finite non-erasing corrective reopening"
  }

canonicalCorrectiveReachability :
  (memory : Memory.MemoryFibre) →
  AdmissibleReach.Reachable
    recoverySystem
    (beforeRecovery memory)
    (afterRecovery memory)
canonicalCorrectiveReachability memory =
  AdmissibleReach.reachableStep
    correctiveEvidence
    (canonicalCorrectiveAction memory)
    AdmissibleReach.reachableRefl

------------------------------------------------------------------------
-- Memory survives while command weighting changes.
------------------------------------------------------------------------

reopeningPreservesRememberedEvent :
  (memory : Memory.MemoryFibre) →
  Memory.rememberedEvent (RecoveryState.memory (afterRecovery memory))
  ≡
  Memory.rememberedEvent (RecoveryState.memory (beforeRecovery memory))
reopeningPreservesRememberedEvent =
  MemoryCommand.extinctionPreservesEventExact

reopeningPreservesProvenance :
  (memory : Memory.MemoryFibre) →
  Memory.memoryProvenance (RecoveryState.memory (afterRecovery memory))
  ≡
  Memory.memoryProvenance (RecoveryState.memory (beforeRecovery memory))
reopeningPreservesProvenance =
  MemoryCommand.extinctionPreservesProvenanceExact

reopeningZerosActionDominance :
  (memory : Memory.MemoryFibre) →
  Memory.actionWeight (RecoveryState.memory (afterRecovery memory))
  ≡
  0
reopeningZerosActionDominance =
  MemoryCommand.extinctionZerosActionWeightExact

------------------------------------------------------------------------
-- The effective accessible subfabric changes.
------------------------------------------------------------------------

reopeningChangesAccessibleFibre :
  (memory : Memory.MemoryFibre) →
  Reach.liveFibreCount (accessible (beforeRecovery memory))
  ≡
  Reach.liveFibreCount (accessible (afterRecovery memory)) →
  ⊥
reopeningChangesAccessibleFibre memory =
  Reach.contractedAndReopenedDiffer

record NonErasingCorrectiveReopening
    (memory : Memory.MemoryFibre) : Set where
  constructor non-erasing-corrective-reopening
  field
    admissibleReachability :
      AdmissibleReach.Reachable
        recoverySystem
        (beforeRecovery memory)
        (afterRecovery memory)
    rememberedEventPreserved :
      Memory.rememberedEvent (RecoveryState.memory (afterRecovery memory))
      ≡
      Memory.rememberedEvent (RecoveryState.memory (beforeRecovery memory))
    provenancePreserved :
      Memory.memoryProvenance (RecoveryState.memory (afterRecovery memory))
      ≡
      Memory.memoryProvenance (RecoveryState.memory (beforeRecovery memory))
    actionDominanceRevised :
      Memory.actionWeight (RecoveryState.memory (afterRecovery memory))
      ≡
      0
    accessibleFibreChanged :
      Reach.liveFibreCount (accessible (beforeRecovery memory))
      ≡
      Reach.liveFibreCount (accessible (afterRecovery memory))
      →
      ⊥

open NonErasingCorrectiveReopening public

canonicalNonErasingCorrectiveReopening :
  (memory : Memory.MemoryFibre) →
  NonErasingCorrectiveReopening memory
canonicalNonErasingCorrectiveReopening memory =
  non-erasing-corrective-reopening
    (canonicalCorrectiveReachability memory)
    (reopeningPreservesRememberedEvent memory)
    (reopeningPreservesProvenance memory)
    (reopeningZerosActionDominance memory)
    (reopeningChangesAccessibleFibre memory)

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record NonErasingReopeningBoundary : Set where
  constructor non-erasing-reopening-boundary
  field
    recoveryRequiresMemoryErasure : Bool
    preservedMemoryRequiresSameCommand : Bool
    correctiveEvidenceMayChangeAccessibleCone : Bool
    finiteWitnessIsClinicalTreatmentClaim : Bool

canonicalNonErasingReopeningBoundary :
  NonErasingReopeningBoundary
canonicalNonErasingReopeningBoundary =
  non-erasing-reopening-boundary
    false false true false
