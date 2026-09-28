module DASHI.Mathematics.Complexity.PNotEqualsNPQ1CoarseFineFutureSafePairExact where

------------------------------------------------------------------------
-- Q1 COARSE/FINE PAIR FUTURE SAFETY
--
-- Coarse construction sharing is allowed to be semantically unsafe.
-- The FINAL pair (coarse work, repair) must be safe.
--
-- This owner makes that distinction exact on a fixed Shannon layer:
--
--   coarse equality alone      need not imply residual-function equality;
--   coarse+repair equality     must imply residual-function equality.
--
-- It is the P-specific form of ObserverRefinementFutureSafetyExact:
-- safe fine does not imply arbitrary coarse safe.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerFibreRepairExact as Repair

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1CoarseFineConstructionSharingExact as Sharing
import DASHI.Core.CoarseFineRelativeFibreExact as CoarseFine

------------------------------------------------------------------------
-- Pair observer.
------------------------------------------------------------------------

q1CoarseRepairObserver :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {ConstructionOutcome RepairCode : Set}
    (sharing :
      Sharing.Q1ConstructionCoarseFine
        {root = root}
        {remaining = remaining}
        ConstructionOutcome)
    (repair :
      Width.LayerNode {root = root} remaining →
      RepairCode) →
  Width.LayerNode {root = root} remaining →
  CoarseFine.Coarse (Sharing.geometry sharing) × RepairCode
q1CoarseRepairObserver sharing repair =
  Observer.pairObserver
    (CoarseFine.coarse (Sharing.geometry sharing))
    repair

------------------------------------------------------------------------
-- Semantic sufficiency of the pair.
------------------------------------------------------------------------

Q1CoarseRepairSemanticSafe :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {ConstructionOutcome RepairCode : Set} →
  (sharing :
    Sharing.Q1ConstructionCoarseFine
      {root = root}
      {remaining = remaining}
      ConstructionOutcome) →
  (repair :
    Width.LayerNode {root = root} remaining →
    RepairCode) →
  Set
Q1CoarseRepairSemanticSafe sharing repair =
  Descent.ConsumerSufficient
    (q1CoarseRepairObserver sharing repair)
    Sharing.layerResidualSemantic

semanticSafePairKernelImpliesResidualEquality :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {ConstructionOutcome RepairCode : Set}
    (sharing :
      Sharing.Q1ConstructionCoarseFine
        {root = root}
        {remaining = remaining}
        ConstructionOutcome)
    (repair :
      Width.LayerNode {root = root} remaining →
      RepairCode) →
  Q1CoarseRepairSemanticSafe sharing repair →
  {left right : Width.LayerNode {root = root} remaining} →
  CoarseFine.coarse (Sharing.geometry sharing) left
    ≡
  CoarseFine.coarse (Sharing.geometry sharing) right →
  repair left ≡ repair right →
  Width.LayerResidualEqual left right
semanticSafePairKernelImpliesResidualEquality
    sharing
    repair
    safe
    sameCoarse
    sameRepair =
  Sharing.consumerEqualityGivesLayerResidualEquality
    (safe
      _
      _
      (cong₂ _,_ sameCoarse sameRepair))

------------------------------------------------------------------------
-- Coarse semantic unsafety may coexist with safe repaired pair.
------------------------------------------------------------------------

record CoarseUnsafeFineSafeWitness
    {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {ConstructionOutcome RepairCode : Set}
    (sharing :
      Sharing.Q1ConstructionCoarseFine
        {root = root}
        {remaining = remaining}
        ConstructionOutcome)
    (repair :
      Width.LayerNode {root = root} remaining →
      RepairCode) : Set₁ where
  constructor coarse-unsafe-fine-safe-witness
  field
    left right :
      Width.LayerNode {root = root} remaining

    sameCoarse :
      CoarseFine.coarse (Sharing.geometry sharing) left
      ≡
      CoarseFine.coarse (Sharing.geometry sharing) right

    residualDifferent :
      Width.LayerResidualEqual left right → ⊥

    pairSafe :
      Q1CoarseRepairSemanticSafe sharing repair

open CoarseUnsafeFineSafeWitness public

coarseUnsafeFineSafeForcesRepairSeparation :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {ConstructionOutcome RepairCode : Set}
    {sharing :
      Sharing.Q1ConstructionCoarseFine
        {root = root}
        {remaining = remaining}
        ConstructionOutcome}
    {repair :
      Width.LayerNode {root = root} remaining →
      RepairCode} →
  (witness : CoarseUnsafeFineSafeWitness sharing repair) →
  repair (left witness) ≡ repair (right witness) →
  ⊥
coarseUnsafeFineSafeForcesRepairSeparation
    {sharing = sharing}
    witness =
  Repair.refinementRepairSeparatesWitness
    (Sharing.sameCoarseDifferentResidualIsSemanticNonDescent
      sharing
      (left witness)
      (right witness)
      (sameCoarse witness)
      (residualDifferent witness))
    (pairSafe witness)

------------------------------------------------------------------------
-- Coarse alone cannot be promoted to a final Q1 semantic code when a witness
-- of this form exists.
------------------------------------------------------------------------

coarseUnsafeFineSafeBlocksCoarseSemanticFactorization :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {ConstructionOutcome RepairCode : Set}
    {sharing :
      Sharing.Q1ConstructionCoarseFine
        {root = root}
        {remaining = remaining}
        ConstructionOutcome}
    {repair :
      Width.LayerNode {root = root} remaining →
      RepairCode} →
  CoarseUnsafeFineSafeWitness sharing repair →
  Descent.FactorsThrough
    (CoarseFine.coarse (Sharing.geometry sharing))
    Sharing.layerResidualSemantic →
  ⊥
coarseUnsafeFineSafeBlocksCoarseSemanticFactorization
    {sharing = sharing}
    witness =
  Sharing.coarseCannotFactorFullResidualSemanticsAcrossCollision
    sharing
    (left witness)
    (right witness)
    (sameCoarse witness)
    (residualDifferent witness)

------------------------------------------------------------------------
-- FRONTIER
--
-- This is the exact architecture B1 is allowed to exploit:
--
--   construction consumer factors through coarse;
--   semantic consumer need not;
--   repaired pair is semantic-safe;
--   any coarse semantic collision is paid by repair separation.
--
-- The remaining question is entirely about the cost/dynamics of producing
-- that repair coordinate, not about permission to merge semantic states.
------------------------------------------------------------------------
