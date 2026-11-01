module DASHI.ComputerScience.FlyCandidateFamilyExecutionAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

import DASHI.Core.CandidateFamilyExecutionExact as Family
import DASHI.ComputerScience.FlyStructureFunctionNDimFibreExact as Fly

------------------------------------------------------------------------
-- FLY NDIM -> GENERIC CANDIDATE-FAMILY EXECUTION
--
-- The Fly owner pays a compatibility/composition architecture but deliberately
-- keeps held-out evaluation, unseen-region generalisation, null rejection, and
-- mechanism promotion separate.  This adapter therefore maps only the finite
-- selection/composition surface into CandidateFamilyExecutionExact.
------------------------------------------------------------------------

flyCandidateFamilyExecutionSpine :
  Family.CandidateFamilyExecutionSpine
flyCandidateFamilyExecutionSpine = record
  { Family = Fly.CompatibleFibreFamily
  ; GlobalAction = Fly.CompatibleFibreFamily
  ; admissibleFamily = λ family →
      Fly.pairwiseConflictFree family ≡ true ×
      Fly.selectedWithoutHeldOutOutcome family ≡ true
  ; compose = λ family → family
  ; globallyAdmissible = λ family →
      Fly.globalCompositionConstructed family ≡ true
  }

admitFlyFamilyComposition :
  (family : Fly.CompatibleFibreFamily) →
  Fly.pairwiseConflictFree family ≡ true →
  Fly.selectedWithoutHeldOutOutcome family ≡ true →
  Fly.globalCompositionConstructed family ≡ true →
  Family.AdmittedCandidateFamilyExecution
    flyCandidateFamilyExecutionSpine
    family
admitFlyFamilyComposition family conflictFree frozenSelection compositionBuilt =
  Family.admitCandidateFamilyExecution
    (conflictFree , frozenSelection)
    compositionBuilt

record FlyCandidateFamilyExecutionBoundary : Set where
  constructor fly-candidate-family-execution-boundary
  field
    existingCompatibleFamilyCarrierReused : Bool
    heldOutOutcomeExcludedFromSelection : Bool
    globalCompositionStillRequired : Bool
    coRequirementRelationInvented : Bool
    globalCompositionPromotedToHeldOutSuccess : Bool
    pairHoldoutPromotedToUnseenRegionGeneralisation : Bool

canonicalFlyCandidateFamilyExecutionBoundary :
  FlyCandidateFamilyExecutionBoundary
canonicalFlyCandidateFamilyExecutionBoundary =
  fly-candidate-family-execution-boundary
    true
    true
    true
    false
    false
    false
