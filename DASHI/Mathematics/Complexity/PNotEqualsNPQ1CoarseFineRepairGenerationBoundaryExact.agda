module DASHI.Mathematics.Complexity.PNotEqualsNPQ1CoarseFineRepairGenerationBoundaryExact where

------------------------------------------------------------------------
-- Q1 COARSE/FINE REPAIR GENERATION BOUNDARY
--
-- Previous owner:
--
--   k distinct residual semantic classes inside one coarse construction fibre
--      -> every sufficient b-bit repair has k <= 2^b.
--
-- This is a REPRESENTATIONAL capacity theorem.
--
-- Repository firewall:
-- RelativeFineModelFidelityOrthogonalityExact explicitly prevents promotion
-- from "different relative-fine information" to "more computation required".
--
-- Therefore the live B1 target is not another cardinality theorem. It is an
-- actual GENERATION/UPDATE mechanism for the relative-fine repair coordinate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Core.CoarseFineRelativeFibreExact as CoarseFine
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.RelativeFineModelFidelityOrthogonalityExact as Orthogonality

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1CoarseFineConstructionSharingExact as Sharing

------------------------------------------------------------------------
-- A fixed-layer action is one Shannon bit.
------------------------------------------------------------------------

LayerAction : Set
LayerAction = Bool

------------------------------------------------------------------------
-- Dynamic coarse+repair generator.
--
-- This is the positive B1 mechanism we actually need:
--
--   * coarse reusable work has its own update;
--   * relative-fine repair has an update that may depend on BOTH coarse and
--     current repair coordinates;
--   * the pair update agrees with the actual Shannon child;
--   * a declared construction consumer factors through the coarse coordinate.
--
-- No cost theorem is hidden in the record.
------------------------------------------------------------------------

record Q1CoarseFineRepairGenerator
    {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (ConstructionOutcome : Set)
    (sharing :
      Sharing.Q1ConstructionCoarseFine
        {root = root}
        {remaining = remaining}
        ConstructionOutcome) : Set₁ where
  constructor q1-coarse-fine-repair-generator
  field
    coarseStep :
      LayerAction →
      CoarseFine.Coarse
        (Sharing.geometry sharing) →
      CoarseFine.Coarse
        (Sharing.geometry sharing)

    repairStep :
      LayerAction →
      CoarseFine.Coarse
        (Sharing.geometry sharing) →
      CoarseFine.RelativeFine
        (Sharing.geometry sharing) →
      CoarseFine.RelativeFine
        (Sharing.geometry sharing)

    -- Fixed-layer nodes cannot themselves take a Shannon step and remain at
    -- the same layer.  The application therefore supplies a child projection
    -- into the next-layer carrier and proves the two coordinates commute.
    NextLayerState :
      Set

    child :
      LayerAction →
      Width.LayerNode {root = root} remaining →
      NextLayerState

    nextCoarse :
      NextLayerState →
      CoarseFine.Coarse
        (Sharing.geometry sharing)

    nextRepair :
      NextLayerState →
      CoarseFine.RelativeFine
        (Sharing.geometry sharing)

    coarseStepExact :
      (action : LayerAction)
      (state : Width.LayerNode {root = root} remaining) →
      nextCoarse (child action state)
      ≡
      coarseStep action
        (CoarseFine.coarse
          (Sharing.geometry sharing)
          state)

    repairStepExact :
      (action : LayerAction)
      (state : Width.LayerNode {root = root} remaining) →
      nextRepair (child action state)
      ≡
      repairStep action
        (CoarseFine.coarse
          (Sharing.geometry sharing)
          state)
        (CoarseFine.relativeFine
          (Sharing.geometry sharing)
          state)

open Q1CoarseFineRepairGenerator public

------------------------------------------------------------------------
-- Pair update.
------------------------------------------------------------------------

pairStep :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {ConstructionOutcome : Set}
    {sharing :
      Sharing.Q1ConstructionCoarseFine
        {root = root}
        {remaining = remaining}
        ConstructionOutcome} →
  Q1CoarseFineRepairGenerator ConstructionOutcome sharing →
  LayerAction →
  CoarseFine.Coarse (Sharing.geometry sharing)
    ×
  CoarseFine.RelativeFine (Sharing.geometry sharing) →
  CoarseFine.Coarse (Sharing.geometry sharing)
    ×
  CoarseFine.RelativeFine (Sharing.geometry sharing)
pairStep generator action (coarse , repair) =
  coarseStep generator action coarse
  ,
  repairStep generator action coarse repair

pairStepExact :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {ConstructionOutcome : Set}
    {sharing :
      Sharing.Q1ConstructionCoarseFine
        {root = root}
        {remaining = remaining}
        ConstructionOutcome}
    (generator :
      Q1CoarseFineRepairGenerator ConstructionOutcome sharing)
    (action : LayerAction)
    (state : Width.LayerNode {root = root} remaining) →
  ( nextCoarse generator
      (child generator action state)
  , nextRepair generator
      (child generator action state)
  )
  ≡
  pairStep generator action
    ( CoarseFine.coarse
        (Sharing.geometry sharing)
        state
    , CoarseFine.relativeFine
        (Sharing.geometry sharing)
        state
    )
pairStepExact generator action state =
  cong₂ _,_
    (coarseStepExact generator action state)
    (repairStepExact generator action state)

------------------------------------------------------------------------
-- Cost accounting is a separate witness.
--
-- In particular, repair coordinate capacity does not determine update cost.
------------------------------------------------------------------------

record Q1CoarseFineRepairGenerationCost
    {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {ConstructionOutcome : Set}
    {sharing :
      Sharing.Q1ConstructionCoarseFine
        {root = root}
        {remaining = remaining}
        ConstructionOutcome}
    (generator :
      Q1CoarseFineRepairGenerator ConstructionOutcome sharing) : Set where
  constructor q1-coarse-fine-repair-generation-cost
  field
    coarseSharedCost : Nat
    fineRepairGenerationCost : Nat
    coordinationCost : Nat
    totalGenerationCost : Nat

    totalCostExact :
      totalGenerationCost
      ≡
      coarseSharedCost
      +
      (fineRepairGenerationCost + coordinationCost)

open Q1CoarseFineRepairGenerationCost public

------------------------------------------------------------------------
-- Firewall: no theorem below derives fineRepairGenerationCost from the size or
-- cardinality of RelativeFine. That promotion requires an application-specific
-- computation model.
------------------------------------------------------------------------

data RepairCapacityImpliesLinearGenerationCost : Set where

repairCapacityDoesNotDefinitionallyGiveLinearWork :
  RepairCapacityImpliesLinearGenerationCost →
  ⊥
repairCapacityDoesNotDefinitionallyGiveLinearWork ()

data Q1RepairGenerationStatus : Set where
  repairCapacityLowerBoundPaid : Q1RepairGenerationStatus
  repairDynamicsInterfacePaid : Q1RepairGenerationStatus
  repairCostDecompositionPaid : Q1RepairGenerationStatus
  sublinearRepairGeneratorPaid : Q1RepairGenerationStatus
  linearRepairWorkLowerBoundPaid : Q1RepairGenerationStatus

currentQ1RepairGenerationStatus :
  Q1RepairGenerationStatus
currentQ1RepairGenerationStatus =
  repairCostDecompositionPaid

------------------------------------------------------------------------
-- B1 FRONTIER
--
-- Paid:
--   semantic width -> repair capacity inside a shared coarse fibre.
--
-- Not licensed:
--   repair capacity -> linear construction work.
--
-- Positive target:
--   construct a real Q1CoarseFineRepairGenerator and a cost witness with
--   fineRepairGenerationCost small enough for the direct-DP strict charge.
--
-- Negative target:
--   prove, for the actual generator model, that producing/updating enough
--   semantically separating repairs forces work comparable to fibre width.
--
-- Either theorem would now be substantive. The abstract coarse/fine calculus
-- alone intentionally decides neither.
------------------------------------------------------------------------
