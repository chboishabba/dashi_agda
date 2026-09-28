module DASHI.Mathematics.Complexity.PNotEqualsNPQ1CoarseFineRepairCapacityExact where

------------------------------------------------------------------------
-- Q1 COARSE-FIBRE REPAIR CAPACITY
--
-- If k pairwise residual-distinct Shannon states share one coarse construction
-- code, then any b-bit repair coordinate sufficient to restore full residual
-- semantics needs capacity for all k classes:
--
--   k <= 2^b.
--
-- Thus coarse construction sharing may move semantic width into the repair
-- coordinate, but cannot erase it.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin.Base using (Fin)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Core.CoarseFineRelativeFibreExact as CoarseFine
import DASHI.Core.ConsumerFibreRepairExact as Repair
import DASHI.Core.GeneralResidualFibreCardinalityExact as Cardinality
import DASHI.Core.ResidualFibreLowerBoundExact as Lower
import DASHI.Core.ObserverRefinementLatticeExact as Observer

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1CoarseFineConstructionSharingExact as Sharing

------------------------------------------------------------------------
-- A residual-width witness concentrated in one coarse construction fibre.
------------------------------------------------------------------------

record WidthWitnessInsideCoarseFibre
    {rootVariables remaining width : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {ConstructionOutcome : Set}
    (sharing :
      Sharing.Q1ConstructionCoarseFine
        {root = root}
        {remaining = remaining}
        ConstructionOutcome)
    (witness :
      Width.ResidualWidthWitness
        {root = root}
        remaining
        width) : Set₁ where
  constructor width-witness-inside-coarse-fibre
  field
    coarseClass :
      CoarseFine.Coarse
        (Sharing.geometry sharing)

    representativeInClass :
      (index : Fin width) →
      CoarseFine.coarse
        (Sharing.geometry sharing)
        (Width.representative witness index)
      ≡
      coarseClass

open WidthWitnessInsideCoarseFibre public

------------------------------------------------------------------------
-- Convert directly to the repository's generic future-distinct-fibre owner,
-- using LayerResidualEqual as the exact fixed-layer future-semantic relation.
------------------------------------------------------------------------

widthWitnessGivesFutureDistinctCoarseFibre :
  ∀ {rootVariables remaining width : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {ConstructionOutcome : Set}
    {sharing :
      Sharing.Q1ConstructionCoarseFine
        {root = root}
        {remaining = remaining}
        ConstructionOutcome}
    {witness :
      Width.ResidualWidthWitness
        {root = root}
        remaining
        width} →
  WidthWitnessInsideCoarseFibre sharing witness →
  Cardinality.FiniteFutureDistinctFibre
    width
    Width.LayerResidualEqual
    (CoarseFine.coarse
      (Sharing.geometry sharing))
widthWitnessGivesFutureDistinctCoarseFibre
    {witness = witness}
    concentrated =
  Cardinality.finiteFutureDistinctFibre
    (Width.representative witness)
    (coarseClass concentrated)
    (representativeInClass concentrated)
    (Width.residualEqualIndicesEqual witness)

------------------------------------------------------------------------
-- A coarse+repair pair sufficient for the residual semantic consumer is
-- dynamically sufficient for LayerResidualEqual.
------------------------------------------------------------------------

semanticRepairGivesDynamicSufficiency :
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
  Repair.RefinementRepairs
    (CoarseFine.coarse
      (Sharing.geometry sharing))
    repair
    Sharing.layerResidualSemantic →
  Lower.DynamicallySufficientPair
    (Width.LayerNode {root = root} remaining)
    (CoarseFine.Coarse
      (Sharing.geometry sharing))
    RepairCode
    Width.LayerResidualEqual
    (CoarseFine.coarse
      (Sharing.geometry sharing))
    repair
semanticRepairGivesDynamicSufficiency
    sharing
    repair
    sufficient =
  Lower.dynamicallySufficientPair
    (λ {left} {right} sameCoarse sameRepair →
      Sharing.consumerEqualityGivesLayerResidualEquality
        (sufficient
          left
          right
          (cong₂ _,_
            sameCoarse
            sameRepair)))
  where
    cong₂ :
      ∀ {A B C : Set}
        (f : A → B → C)
        {a a′ : A}
        {b b′ : B} →
      a ≡ a′ →
      b ≡ b′ →
      f a b ≡ f a′ b′
    cong₂ f refl refl =
      refl

------------------------------------------------------------------------
-- Main capacity theorem.
------------------------------------------------------------------------

coarseFibreWidthForcesBitRepairCapacity :
  ∀ {rootVariables remaining width bits : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {ConstructionOutcome : Set}
    (sharing :
      Sharing.Q1ConstructionCoarseFine
        {root = root}
        {remaining = remaining}
        ConstructionOutcome)
    (witness :
      Width.ResidualWidthWitness
        {root = root}
        remaining
        width)
    (concentrated :
      WidthWitnessInsideCoarseFibre
        sharing
        witness)
    (repair :
      Width.LayerNode {root = root} remaining →
      Cardinality.BitWords bits) →
  Repair.RefinementRepairs
    (CoarseFine.coarse
      (Sharing.geometry sharing))
    repair
    Sharing.layerResidualSemantic →
  width
  ≤
  Cardinality.pow2 bits
coarseFibreWidthForcesBitRepairCapacity
    sharing
    witness
    concentrated
    repair
    sufficient =
  Cardinality.futureSafetyForBitWordsImpliesCapacityBound
    (semanticRepairGivesDynamicSufficiency
      sharing
      repair
      sufficient)
    (widthWitnessGivesFutureDistinctCoarseFibre
      concentrated)

------------------------------------------------------------------------
-- Exact relative-fine reopening also gives dynamic sufficiency immediately:
-- equal coarse + equal relativeFine means the original layer node is equal.
------------------------------------------------------------------------

relativeFineReopeningIsDynamicallySufficient :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {ConstructionOutcome : Set}
    (sharing :
      Sharing.Q1ConstructionCoarseFine
        {root = root}
        {remaining = remaining}
        ConstructionOutcome) →
  Lower.DynamicallySufficientPair
    (Width.LayerNode {root = root} remaining)
    (CoarseFine.Coarse
      (Sharing.geometry sharing))
    (CoarseFine.RelativeFine
      (Sharing.geometry sharing))
    Width.LayerResidualEqual
    (CoarseFine.coarse
      (Sharing.geometry sharing))
    (CoarseFine.relativeFine
      (Sharing.geometry sharing))
relativeFineReopeningIsDynamicallySufficient sharing =
  Lower.dynamicallySufficientPair
    (λ sameCoarse sameFine →
      Sharing.layerNodeEqualityGivesLayerResidualEquality
        (Sharing.coarseFinePairDeterminesLayerNode
          sharing
          sameCoarse
          sameFine))

------------------------------------------------------------------------
-- If the actual relative-fine coordinate is itself a fixed b-bit code, the
-- same capacity lower bound follows without any extra semantic-repair premise.
------------------------------------------------------------------------

record BitRelativeFineRealization
    {rootVariables remaining bits : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {ConstructionOutcome : Set}
    (sharing :
      Sharing.Q1ConstructionCoarseFine
        {root = root}
        {remaining = remaining}
        ConstructionOutcome) : Set₁ where
  constructor bit-relative-fine-realization
  field
    encodeRelativeFine :
      CoarseFine.RelativeFine
        (Sharing.geometry sharing) →
      Cardinality.BitWords bits

    encodeRelativeFineInjective :
      ∀ {left right} →
      encodeRelativeFine left
      ≡
      encodeRelativeFine right →
      left ≡ right

open BitRelativeFineRealization public

encodedRelativeFine :
  ∀ {rootVariables remaining bits : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {ConstructionOutcome : Set}
    {sharing :
      Sharing.Q1ConstructionCoarseFine
        {root = root}
        {remaining = remaining}
        ConstructionOutcome} →
  BitRelativeFineRealization
    {bits = bits}
    sharing →
  Width.LayerNode {root = root} remaining →
  Cardinality.BitWords bits
encodedRelativeFine realization node =
  encodeRelativeFine realization
    (CoarseFine.relativeFine
      (Sharing.geometry _)
      node)

encodedRelativeFineIsDynamicallySufficient :
  ∀ {rootVariables remaining bits : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {ConstructionOutcome : Set}
    (sharing :
      Sharing.Q1ConstructionCoarseFine
        {root = root}
        {remaining = remaining}
        ConstructionOutcome)
    (realization :
      BitRelativeFineRealization
        {bits = bits}
        sharing) →
  Lower.DynamicallySufficientPair
    (Width.LayerNode {root = root} remaining)
    (CoarseFine.Coarse
      (Sharing.geometry sharing))
    (Cardinality.BitWords bits)
    Width.LayerResidualEqual
    (CoarseFine.coarse
      (Sharing.geometry sharing))
    (encodedRelativeFine realization)
encodedRelativeFineIsDynamicallySufficient
    sharing
    realization =
  Lower.dynamicallySufficientPair
    (λ sameCoarse sameEncoded →
      Sharing.layerNodeEqualityGivesLayerResidualEquality
        (Sharing.coarseFinePairDeterminesLayerNode
          sharing
          sameCoarse
          (encodeRelativeFineInjective
            realization
            sameEncoded)))

coarseFibreWidthForcesActualRelativeFineCapacity :
  ∀ {rootVariables remaining width bits : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {ConstructionOutcome : Set}
    (sharing :
      Sharing.Q1ConstructionCoarseFine
        {root = root}
        {remaining = remaining}
        ConstructionOutcome)
    (witness :
      Width.ResidualWidthWitness
        {root = root}
        remaining
        width)
    (concentrated :
      WidthWitnessInsideCoarseFibre
        sharing
        witness)
    (realization :
      BitRelativeFineRealization
        {bits = bits}
        sharing) →
  width
  ≤
  Cardinality.pow2 bits
coarseFibreWidthForcesActualRelativeFineCapacity
    sharing
    witness
    concentrated
    realization =
  Cardinality.futureSafetyForBitWordsImpliesCapacityBound
    (encodedRelativeFineIsDynamicallySufficient
      sharing
      realization)
    (widthWitnessGivesFutureDistinctCoarseFibre
      concentrated)

------------------------------------------------------------------------
-- B1 CONSEQUENCE
--
-- Coarse sharing can reduce repeated CONSTRUCTION work, but inside any coarse
-- fibre containing k distinct residual semantic classes, a b-bit sufficient
-- repair must satisfy
--
--   k <= 2^b.
--
-- Hence semantic width is displaced into repair capacity, not eliminated.
-- What remains open is computational rather than representational:
--
--   can those k distinct repair values be generated/updated with sub-k charged
--   work from a shared generative mechanism?
--
-- That generative repair theorem is now the precise positive B1 target.
------------------------------------------------------------------------
