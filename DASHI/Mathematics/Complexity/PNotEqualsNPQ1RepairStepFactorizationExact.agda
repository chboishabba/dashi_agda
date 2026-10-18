module DASHI.Mathematics.Complexity.PNotEqualsNPQ1RepairStepFactorizationExact where

------------------------------------------------------------------------
-- PRE-GENERATOR FACTORIZATION TEST FOR COMPRESSED Q1 REPAIR
--
-- A proposed compressed representation should be testable BEFORE we assume an
-- exact repairStep exists.
--
-- Projection:
--   parent node -> (coarse, repair).
--
-- Question:
--   does the required child repair factor through
--
--       (action, parent coarse, parent repair) ?
--
-- If two parents collide on the generator input but their same-action child
-- repairs differ, factorization is impossible.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1GradedShannonRepairGeneratorExact as Shannon

record GradedQ1RepairProjection
    {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) : Set₁ where
  field
    Coarse : Nat → Set
    Repair : Nat → Set

    coarse :
      (remaining : Nat) →
      Width.LayerNode {root = root} remaining →
      Coarse remaining

    repair :
      (remaining : Nat) →
      Width.LayerNode {root = root} remaining →
      Repair remaining

open GradedQ1RepairProjection public

record RepairStepFactorization
    {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (projection : GradedQ1RepairProjection root) : Set₁ where
  field
    repairStep :
      (remaining : Nat) →
      Bool →
      Coarse projection (suc remaining) →
      Repair projection (suc remaining) →
      Repair projection remaining

    repairStepExact :
      (remaining : Nat) →
      (action : Bool) →
      (parent : Width.LayerNode {root = root} (suc remaining)) →
      repair projection remaining
        (Shannon.layerChild action parent)
      ≡
      repairStep remaining action
        (coarse projection (suc remaining) parent)
        (repair projection (suc remaining) parent)

open RepairStepFactorization public

record RepairStepNonFactorizationWitness
    {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (projection : GradedQ1RepairProjection root) : Set₁ where
  constructor repair-step-non-factorization-witness
  field
    action : Bool

    leftParent rightParent :
      Width.LayerNode {root = root} (suc remaining)

    sameCoarse :
      coarse projection (suc remaining) leftParent
      ≡
      coarse projection (suc remaining) rightParent

    sameRepair :
      repair projection (suc remaining) leftParent
      ≡
      repair projection (suc remaining) rightParent

    differentRequiredChildRepair :
      repair projection remaining
        (Shannon.layerChild action leftParent)
      ≡
      repair projection remaining
        (Shannon.layerChild action rightParent) →
      ⊥

open RepairStepNonFactorizationWitness public

nonFactorizationWitnessBlocksRepairStep :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {projection : GradedQ1RepairProjection root} →
  RepairStepNonFactorizationWitness
    {remaining = remaining}
    projection →
  RepairStepFactorization projection →
  ⊥
nonFactorizationWitnessBlocksRepairStep
    {remaining = remaining}
    {projection = projection}
    witness
    factors =
  differentRequiredChildRepair witness
    (trans
      (repairStepExact factors
        remaining
        (action witness)
        (leftParent witness))
      (trans
        (cong₂
          (repairStep factors remaining (action witness))
          (sameCoarse witness)
          (sameRepair witness))
        (sym
          (repairStepExact factors
            remaining
            (action witness)
            (rightParent witness)))))

------------------------------------------------------------------------
-- Full-node baseline factors.
------------------------------------------------------------------------

fullNodeProjection :
  ∀ {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) →
  GradedQ1RepairProjection root
fullNodeProjection root =
  record
    { Coarse =
        Shannon.Coarse (Shannon.fullNodeRepairGenerator root)
    ; Repair =
        Shannon.Repair (Shannon.fullNodeRepairGenerator root)
    ; coarse =
        Shannon.coarse (Shannon.fullNodeRepairGenerator root)
    ; repair =
        Shannon.repair (Shannon.fullNodeRepairGenerator root)
    }

fullNodeProjectionFactors :
  ∀ {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) →
  RepairStepFactorization
    (fullNodeProjection root)
fullNodeProjectionFactors root =
  record
    { repairStep =
        Shannon.repairStep
          (Shannon.fullNodeRepairGenerator root)
    ; repairStepExact =
        Shannon.repairStepExact
          (Shannon.fullNodeRepairGenerator root)
    }

------------------------------------------------------------------------
-- FRONTIER
--
-- This is now an executable search protocol for P:
--
-- 1. propose a compressed coarse/repair projection;
-- 2. try to construct RepairStepFactorization;
-- 3. if it fails, search for RepairStepNonFactorizationWitness.
--
-- A collision witness is exact evidence that the proposed repair state omits
-- information required by one-step Shannon evolution.
------------------------------------------------------------------------
