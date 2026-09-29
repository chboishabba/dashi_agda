module DASHI.Mathematics.Complexity.PNotEqualsNPQ1CoarseFineConstructionSharingExact where

------------------------------------------------------------------------
-- Q1 COARSE / FINE CONSTRUCTION SHARING
--
-- B1 is not "may two semantically distinct residuals share one Q1 state?"
-- Residual-width theory already forbids that.
--
-- The admissible possibility is:
--
--   fine restriction node
--      = (coarse reusable construction work, relative-fine semantic repair).
--
-- The coarse coordinate may be sufficient for a declared CONSTRUCTION
-- consumer while being insufficient for the full residual Boolean-function
-- consumer. Exact reopening then retains the semantic distinction in the
-- relative-fine coordinate.
--
-- This module is a P-specific adapter over the repository-native coarse/fine,
-- consumer-factorization and fibre-repair kernels.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin)
open import Relation.Binary.PropositionalEquality using (_≢_; cong; sym)

import DASHI.Core.CoarseFineRelativeFibreExact as CoarseFine
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerFibreRepairExact as Repair
import DASHI.Core.ObserverRefinementLatticeExact as Observer

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalFutureCongruenceExact as Future

------------------------------------------------------------------------
-- Fixed-layer residual semantic consumer.
------------------------------------------------------------------------

ResidualSemantic :
  Nat →
  Set
ResidualSemantic remaining =
  SAT.Assignment remaining →
  Bool

residualSemantic :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  Width.LayerNode {root = root} remaining →
  ResidualSemantic remaining
residualSemantic node assignment =
  SAT.evaluate
    (Family.currentFormula (Width.node node))
    (Future.transportAssignment
      (Agda.Builtin.Equality.primTrustMe)
      assignment)

------------------------------------------------------------------------
-- Avoid proof-irrelevance assumptions by defining the exact semantic consumer
-- with the same transport used by LayerResidualEqual.
------------------------------------------------------------------------

layerResidualSemantic :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  Width.LayerNode {root = root} remaining →
  ResidualSemantic remaining
layerResidualSemantic node assignment =
  SAT.evaluate
    (Family.currentFormula (Width.node node))
    (Future.transportAssignment
      (sym
        (Width.arityExact node))
      assignment)

consumerEqualityGivesLayerResidualEquality :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {left right : Width.LayerNode {root = root} remaining} →
  layerResidualSemantic left
  ≡
  layerResidualSemantic right →
  Width.LayerResidualEqual left right
consumerEqualityGivesLayerResidualEquality same assignment =
  cong
    (λ consumer → consumer assignment)
    same

layerNodeEqualityGivesLayerResidualEquality :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {left right : Width.LayerNode {root = root} remaining} →
  left ≡ right →
  Width.LayerResidualEqual left right
layerNodeEqualityGivesLayerResidualEquality refl assignment =
  refl

------------------------------------------------------------------------
-- Coarse/fine construction-sharing package.
------------------------------------------------------------------------

record Q1ConstructionCoarseFine
    {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (ConstructionOutcome : Set) : Set₁ where
  constructor q1-construction-coarse-fine
  field
    geometry :
      CoarseFine.CoarseFineReopening
        (Width.LayerNode {root = root} remaining)

    constructionConsumer :
      Width.LayerNode {root = root} remaining →
      ConstructionOutcome

    constructionFactorsThroughCoarse :
      Descent.FactorsThrough
        (CoarseFine.coarse geometry)
        constructionConsumer

open Q1ConstructionCoarseFine public

------------------------------------------------------------------------
-- The pair (coarse, relativeFine) is exact and separating by inherited core
-- theorems.
------------------------------------------------------------------------

coarseFinePairDeterminesLayerNode :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {ConstructionOutcome : Set}
    (sharing :
      Q1ConstructionCoarseFine
        {root = root}
        {remaining = remaining}
        ConstructionOutcome)
    {left right : Width.LayerNode {root = root} remaining} →
  CoarseFine.coarse (geometry sharing) left
  ≡
  CoarseFine.coarse (geometry sharing) right →
  CoarseFine.relativeFine (geometry sharing) left
  ≡
  CoarseFine.relativeFine (geometry sharing) right →
  left ≡ right
coarseFinePairDeterminesLayerNode sharing =
  CoarseFine.coarseAndRelativeFineDetermineState
    (geometry sharing)

------------------------------------------------------------------------
-- Same coarse work + different residual semantics forces the relative-fine
-- coordinate to separate.
------------------------------------------------------------------------

sameCoarseDifferentResidualForcesFineRepair :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {ConstructionOutcome : Set}
    (sharing :
      Q1ConstructionCoarseFine
        {root = root}
        {remaining = remaining}
        ConstructionOutcome)
    {left right : Width.LayerNode {root = root} remaining} →
  CoarseFine.coarse (geometry sharing) left
  ≡
  CoarseFine.coarse (geometry sharing) right →
  (Width.LayerResidualEqual left right → ⊥) →
  CoarseFine.relativeFine (geometry sharing) left
  ≡
  CoarseFine.relativeFine (geometry sharing) right →
  ⊥
sameCoarseDifferentResidualForcesFineRepair
    sharing
    sameCoarse
    residualDifferent
    sameFine =
  residualDifferent
    (layerNodeEqualityGivesLayerResidualEquality
      (coarseFinePairDeterminesLayerNode
        sharing
        sameCoarse
        sameFine))

------------------------------------------------------------------------
-- Coarse collision is an explicit non-factorization witness for the residual
-- semantic consumer.
------------------------------------------------------------------------

sameCoarseDifferentResidualIsSemanticNonDescent :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {ConstructionOutcome : Set}
    (sharing :
      Q1ConstructionCoarseFine
        {root = root}
        {remaining = remaining}
        ConstructionOutcome)
    (left right : Width.LayerNode {root = root} remaining) →
  CoarseFine.coarse (geometry sharing) left
  ≡
  CoarseFine.coarse (geometry sharing) right →
  (Width.LayerResidualEqual left right → ⊥) →
  Descent.ConsumerNonDescentWitness
    (CoarseFine.coarse (geometry sharing))
    layerResidualSemantic
sameCoarseDifferentResidualIsSemanticNonDescent
    sharing
    left
    right
    sameCoarse
    residualDifferent =
  Descent.consumerNonDescentWitness
    left
    right
    sameCoarse
    (λ sameConsumer →
      residualDifferent
        (consumerEqualityGivesLayerResidualEquality
          sameConsumer))

coarseCannotFactorFullResidualSemanticsAcrossCollision :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {ConstructionOutcome : Set}
    (sharing :
      Q1ConstructionCoarseFine
        {root = root}
        {remaining = remaining}
        ConstructionOutcome)
    (left right : Width.LayerNode {root = root} remaining) →
  CoarseFine.coarse (geometry sharing) left
  ≡
  CoarseFine.coarse (geometry sharing) right →
  (Width.LayerResidualEqual left right → ⊥) →
  Descent.FactorsThrough
    (CoarseFine.coarse (geometry sharing))
    layerResidualSemantic →
  ⊥
coarseCannotFactorFullResidualSemanticsAcrossCollision
    sharing
    left
    right
    sameCoarse
    residualDifferent
    factors =
  Descent.nonDescentWitnessBlocksFactorization
    (sameCoarseDifferentResidualIsSemanticNonDescent
      sharing
      left
      right
      sameCoarse
      residualDifferent)
    factors

------------------------------------------------------------------------
-- Any alternative repair coordinate which DOES make the coarse+repair pair
-- sufficient for residual semantics must separate the collision.
------------------------------------------------------------------------

everySemanticRepairSeparatesSameCoarseResidualCollision :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {ConstructionOutcome RepairCode : Set}
    (sharing :
      Q1ConstructionCoarseFine
        {root = root}
        {remaining = remaining}
        ConstructionOutcome)
    (repair :
      Width.LayerNode {root = root} remaining →
      RepairCode)
    (left right : Width.LayerNode {root = root} remaining) →
  CoarseFine.coarse (geometry sharing) left
  ≡
  CoarseFine.coarse (geometry sharing) right →
  (Width.LayerResidualEqual left right → ⊥) →
  Repair.RefinementRepairs
    (CoarseFine.coarse (geometry sharing))
    repair
    layerResidualSemantic →
  repair left ≡ repair right →
  ⊥
everySemanticRepairSeparatesSameCoarseResidualCollision
    sharing
    repair
    left
    right
    sameCoarse
    residualDifferent
    repaired
    sameRepair =
  Repair.refinementRepairSeparatesWitness
    (sameCoarseDifferentResidualIsSemanticNonDescent
      sharing
      left
      right
      sameCoarse
      residualDifferent)
    repaired
    sameRepair

------------------------------------------------------------------------
-- Construction factorization and semantic factorization are independent.
--
-- The package assumes only the former. A witnessed coarse collision between
-- distinct residual functions proves the latter is impossible on that fibre.
------------------------------------------------------------------------

constructionConsumerFactorsThroughCoarse :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {ConstructionOutcome : Set}
    (sharing :
      Q1ConstructionCoarseFine
        {root = root}
        {remaining = remaining}
        ConstructionOutcome) →
  Descent.FactorsThrough
    (CoarseFine.coarse (geometry sharing))
    (constructionConsumer sharing)
constructionConsumerFactorsThroughCoarse =
  constructionFactorsThroughCoarse

------------------------------------------------------------------------
-- Width-family repair consequence.
--
-- A residual-width witness enumerates nodes whose residual semantics are
-- pairwise distinct. If any two representatives collide in the coarse work
-- code, the relative-fine coordinate (and every sufficient semantic repair)
-- must separate that pair.
------------------------------------------------------------------------

widthWitnessCoarseCollisionForcesRelativeFineSeparation :
  ∀ {rootVariables remaining width : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {ConstructionOutcome : Set}
    (sharing :
      Q1ConstructionCoarseFine
        {root = root}
        {remaining = remaining}
        ConstructionOutcome)
    (witness :
      Width.ResidualWidthWitness
        {root = root}
        remaining
        width)
    {leftIndex rightIndex : Fin width} →
  CoarseFine.coarse
      (geometry sharing)
      (Width.representative witness leftIndex)
  ≡
  CoarseFine.coarse
      (geometry sharing)
      (Width.representative witness rightIndex) →
  leftIndex ≢ rightIndex →
  CoarseFine.relativeFine
      (geometry sharing)
      (Width.representative witness leftIndex)
  ≡
  CoarseFine.relativeFine
      (geometry sharing)
      (Width.representative witness rightIndex) →
  ⊥
widthWitnessCoarseCollisionForcesRelativeFineSeparation
    sharing
    witness
    sameCoarse
    indicesDifferent
    sameFine =
  indicesDifferent
    (Width.residualEqualIndicesEqual
      witness
      (layerNodeEqualityGivesLayerResidualEquality
        (coarseFinePairDeterminesLayerNode
          sharing
          sameCoarse
          sameFine)))

------------------------------------------------------------------------
-- B1 CONSEQUENCE
--
-- Coarse sharing is legitimate only as construction reuse.
--
-- It cannot erase semantic width:
--
--   same coarse + different residual function
--       -> relativeFine differs,
--
-- and any alternative refinement sufficient for the residual semantic
-- consumer must also separate that collision.
--
-- Therefore a useful B1 mechanism must compress the COST of producing or
-- updating the relative-fine repairs. It cannot identify semantically distinct
-- repairs as one Q1 state.
--
-- The next quantitative question is whether repair generation itself admits a
-- shared generative representation whose charged update cost is sublinear in
-- the number of residual semantic classes.
------------------------------------------------------------------------
