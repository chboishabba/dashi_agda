module DASHI.Mathematics.Complexity.PNotEqualsNPQ1GradedShannonRepairGeneratorExact where

------------------------------------------------------------------------
-- ACTUAL GRADED SHANNON REPAIR GENERATION
--
-- Shannon restriction changes remaining arity:
--
--   layer (suc r) --false/true--> layer r.
--
-- Therefore the honest generator is graded by r.  This owner gives the most
-- favorable possible positive baseline: let the repair coordinate retain the
-- ENTIRE restriction node. Then repairStep is literally falseChild/trueChild.
--
-- This proves that recursive generation itself is not impossible. What remains
-- is compression: can a strictly smaller repair code support the same exact
-- graded transition while preserving future semantics?
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width

------------------------------------------------------------------------
-- Actual Shannon child on fixed-layer packages.
------------------------------------------------------------------------

falseLayerChild :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  Width.LayerNode {root = root} (suc remaining) →
  Width.LayerNode {root = root} remaining
falseLayerChild {remaining = remaining} layer
    with Width.node layer | Width.arityExact layer
... | Family.restriction-node .(suc remaining) current derivation | refl =
  Width.layer-node
    (Family.falseChild derivation)
    refl

trueLayerChild :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  Width.LayerNode {root = root} (suc remaining) →
  Width.LayerNode {root = root} remaining
trueLayerChild {remaining = remaining} layer
    with Width.node layer | Width.arityExact layer
... | Family.restriction-node .(suc remaining) current derivation | refl =
  Width.layer-node
    (Family.trueChild derivation)
    refl

layerChild :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  Bool →
  Width.LayerNode {root = root} (suc remaining) →
  Width.LayerNode {root = root} remaining
layerChild false =
  falseLayerChild
layerChild true =
  trueLayerChild

------------------------------------------------------------------------
-- General graded coarse/fine repair generator.
------------------------------------------------------------------------

record GradedQ1RepairGenerator
    {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) : Set₁ where
  field
    Coarse :
      Nat → Set

    Repair :
      Nat → Set

    coarse :
      (remaining : Nat) →
      Width.LayerNode {root = root} remaining →
      Coarse remaining

    repair :
      (remaining : Nat) →
      Width.LayerNode {root = root} remaining →
      Repair remaining

    repairStep :
      (remaining : Nat) →
      Bool →
      Coarse (suc remaining) →
      Repair (suc remaining) →
      Repair remaining

    repairStepExact :
      (remaining : Nat) →
      (action : Bool) →
      (parent : Width.LayerNode {root = root} (suc remaining)) →
      repair remaining
        (layerChild action parent)
      ≡
      repairStep remaining action
        (coarse (suc remaining) parent)
        (repair (suc remaining) parent)

open GradedQ1RepairGenerator public

------------------------------------------------------------------------
-- Baseline: coarse carries no information, repair retains the full node.
------------------------------------------------------------------------

fullNodeRepairGenerator :
  ∀ {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) →
  GradedQ1RepairGenerator root
fullNodeRepairGenerator root =
  record
    { Coarse =
        λ remaining → ⊤
    ; Repair =
        λ remaining →
          Width.LayerNode {root = root} remaining
    ; coarse =
        λ remaining node → tt
    ; repair =
        λ remaining node → node
    ; repairStep =
        λ remaining action coarse parent →
          layerChild action parent
    ; repairStepExact =
        λ remaining action parent → refl
    }

fullNodeRepairStepIsActualShannonChild :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (action : Bool)
    (parent : Width.LayerNode {root = root} (suc remaining)) →
  repairStep
      (fullNodeRepairGenerator root)
      remaining
      action
      tt
      parent
  ≡
  layerChild action parent
fullNodeRepairStepIsActualShannonChild action parent =
  refl

------------------------------------------------------------------------
-- Full-node repair is semantically sufficient by identity.
------------------------------------------------------------------------

fullNodeRepairEqualityImpliesResidualEquality :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {left right : Width.LayerNode {root = root} remaining} →
  repair
      (fullNodeRepairGenerator root)
      remaining
      left
  ≡
  repair
      (fullNodeRepairGenerator root)
      remaining
      right →
  Width.LayerResidualEqual left right
fullNodeRepairEqualityImpliesResidualEquality refl assignment =
  refl

------------------------------------------------------------------------
-- Exact factorability collision for ANY proposed smaller repair generator.
--
-- If two parents present the same generator input (same coarse, same repair)
-- under the same action but their required child repair values differ, then no
-- exact repairStep can satisfy both.
------------------------------------------------------------------------

record RepairStepCollision
    {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (generator : GradedQ1RepairGenerator root) : Set₁ where
  constructor repair-step-collision
  field
    action :
      Bool

    leftParent rightParent :
      Width.LayerNode {root = root} (suc remaining)

    sameCoarse :
      coarse generator (suc remaining) leftParent
      ≡
      coarse generator (suc remaining) rightParent

    sameRepair :
      repair generator (suc remaining) leftParent
      ≡
      repair generator (suc remaining) rightParent

    childRepairDifferent :
      repair generator remaining
        (layerChild action leftParent)
      ≡
      repair generator remaining
        (layerChild action rightParent) →
      ⊥

open RepairStepCollision public

repairStepCollisionImpossible :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {generator : GradedQ1RepairGenerator root} →
  RepairStepCollision {remaining = remaining} generator →
  ⊥
repairStepCollisionImpossible
    {remaining = remaining}
    {generator = generator}
    collision =
  childRepairDifferent collision
    (trans
      (repairStepExact generator
        remaining
        (action collision)
        (leftParent collision))
      (trans
        (cong₂
          (repairStep generator remaining (action collision))
          (sameCoarse collision)
          (sameRepair collision))
        (sym
          (repairStepExact generator
            remaining
            (action collision)
            (rightParent collision)))))
------------------------------------------------------------------------
-- FRONTIER
--
-- Positive baseline PAID:
--
--   R_rho = the entire restriction node
--   R_(a rho) = actual Shannon child(a, R_rho).
--
-- This is exact but provides no compression.
--
-- A substantive compressed generator must choose smaller Coarse/Repair
-- coordinates and still inhabit repairStepExact.
--
-- Fast falsification criterion:
--   find two parents with the same (coarse, repair) generator input whose
--   same-action children require different repair outputs.
--
-- Such a witness is literally incompatible with any deterministic local
-- repairStep through (action, coarse, current repair).
------------------------------------------------------------------------
