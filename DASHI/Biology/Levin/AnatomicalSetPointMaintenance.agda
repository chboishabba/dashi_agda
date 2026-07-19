module DASHI.Biology.Levin.AnatomicalSetPointMaintenance where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.PatternMemoryCore as Memory
import DASHI.Biology.Levin.HierarchicalGoalMemory as Hierarchy
import DASHI.Biology.Levin.ProblemSpaceAgency as ProblemSpace

------------------------------------------------------------------------
-- Large-scale anatomical maintenance under continual material turnover.

record AnatomicalMaintenanceWitness : Set where
  field
    targetMorphologyStored       : Bool
    localDamageObservable        : Bool
    globalMismatchObservable     : Bool
    correctiveActivityTriggered  : Bool
    repairStopsNearTarget        : Bool
    componentTurnoverPermitted   : Bool
    targetRewriteSeparatelyTyped : Bool
    interpretation              : String

record AnatomicalSetPointBoundary : Set where
  field
    memoryBoundary       : Memory.PatternMemoryBoundary
    hierarchyBoundary    : Hierarchy.HierarchicalGoalMemoryBoundary
    problemSpaceBoundary : ProblemSpace.ProblemSpaceAgencyBoundary
    setPointNotPresentShape : Bool
    successfulRepairNotProofOfRepresentation : Bool
    maintenanceNotImmortality : Bool
    enhancementNeedsNewTargetWitness : Bool
    clinicalAuthorityBlocked : Bool

canonicalAnatomicalMaintenanceWitness : AnatomicalMaintenanceWitness
canonicalAnatomicalMaintenanceWitness = record
  { targetMorphologyStored = true
  ; localDamageObservable = true
  ; globalMismatchObservable = true
  ; correctiveActivityTriggered = true
  ; repairStopsNearTarget = true
  ; componentTurnoverPermitted = true
  ; targetRewriteSeparatelyTyped = true
  ; interpretation = "A body-level maintenance process may preserve a target morphology through component turnover by detecting mismatch and stopping correction near a typed set point"
  }

canonicalAnatomicalSetPointBoundary : AnatomicalSetPointBoundary
canonicalAnatomicalSetPointBoundary = record
  { memoryBoundary = Memory.canonicalPatternMemoryBoundary
  ; hierarchyBoundary = Hierarchy.canonicalHierarchicalGoalMemoryBoundary
  ; problemSpaceBoundary = ProblemSpace.canonicalProblemSpaceAgencyBoundary
  ; setPointNotPresentShape = true
  ; successfulRepairNotProofOfRepresentation = true
  ; maintenanceNotImmortality = true
  ; enhancementNeedsNewTargetWitness = true
  ; clinicalAuthorityBlocked = true
  }
