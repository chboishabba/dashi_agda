module DASHI.Physics.YangMills.BalabanClayGate4WilsonPlaquetteBadCubeBudgetExact where

open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as Gap
import DASHI.Physics.YangMills.BalabanClayGate4LiteralWilsonLargeFieldPredicateExact as Wilson
import DASHI.Physics.YangMills.BalabanClayGate4DimockLargeFieldSuppressionExact as LargeField

------------------------------------------------------------------------
-- Literal Wilson bad-cube penalty.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. I. The Basic Step of the R Operation",
-- Communications in Mathematical Physics 122 (1989), 175--202.
-- DOI: 10.1007/BF01257412.
--
-- For a plaquette-bad cube the exact SU(2) trace/chordal identity gives the
-- local action penalty
--
--   p_bad = (beta/2) eta^2.
--
-- The finite large-region theorem then needs only the explicit scalar check
-- entropy + reserved slack <= p_bad.  No separate physical penalty field is
-- accepted by this adapter.
------------------------------------------------------------------------

rationalOrderedAdditiveBudget :
  Gap.RationalWilsonGapOrder → LargeField.OrderedAdditiveBudget ℚ
rationalOrderedAdditiveBudget order = record
  { zero = 0ℚ
  ; add = _+_
  ; LessEqual = _≤_
  ; reflexive = Gap.reflexive order
  ; transitive = Gap.transitive order
  ; addMonotone = Gap.addMonotone order
  }

record WilsonPlaquetteBadCubeBudget
    {Scale Configuration Gauge Block Plaquette : Set}
    (largeField : Wilson.LiteralWilsonLargeFieldData
      Scale Configuration Gauge Block Plaquette)
    (cost : Wilson.LiteralWilsonCostData largeField) : Set₁ where
  field
    scale : Scale
    entropyPerBadCube reservedSlackPerBadCube : ℚ

    entropyAndSlackBelowWilsonPenalty :
      entropyPerBadCube + reservedSlackPerBadCube
      ≤
      (Gap.halfℚ * Wilson.beta cost scale)
        * Gap.squareℚ (Wilson.threshold largeField scale)

open WilsonPlaquetteBadCubeBudget public

wilsonPenaltyPerBadCube :
  ∀ {Scale Configuration Gauge Block Plaquette}
    {largeField : Wilson.LiteralWilsonLargeFieldData
      Scale Configuration Gauge Block Plaquette}
    {cost : Wilson.LiteralWilsonCostData largeField} →
  WilsonPlaquetteBadCubeBudget largeField cost → ℚ
wilsonPenaltyPerBadCube {largeField = largeField} {cost = cost} budget =
  (Gap.halfℚ * Wilson.beta cost (scale budget))
    * Gap.squareℚ (Wilson.threshold largeField (scale budget))

asLargeFieldCubeBudget :
  ∀ {Scale Configuration Gauge Block Plaquette}
    {largeField : Wilson.LiteralWilsonLargeFieldData
      Scale Configuration Gauge Block Plaquette}
    {cost : Wilson.LiteralWilsonCostData largeField} →
  (budget : WilsonPlaquetteBadCubeBudget largeField cost) →
  LargeField.LargeFieldCubeBudget ℚ
asLargeFieldCubeBudget {cost = cost} budget = record
  { algebra =
      rationalOrderedAdditiveBudget (Wilson.order cost)
  ; entropyPerBadCube =
      entropyPerBadCube budget
  ; reservedSlackPerBadCube =
      reservedSlackPerBadCube budget
  ; penaltyPerBadCube =
      wilsonPenaltyPerBadCube budget
  ; penaltyPaysEntropyAndSlack =
      entropyAndSlackBelowWilsonPenalty budget
  }

largePlaquettePaysWilsonBadCubePenalty :
  ∀ {Scale Configuration Gauge Block Plaquette}
    {largeField : Wilson.LiteralWilsonLargeFieldData
      Scale Configuration Gauge Block Plaquette}
    {cost : Wilson.LiteralWilsonCostData largeField}
    (budget : WilsonPlaquetteBadCubeBudget largeField cost)
    configuration plaquette →
  Wilson.LargePlaquette largeField (scale budget) configuration plaquette →
  wilsonPenaltyPerBadCube budget
  ≤ Wilson.scaledWilsonPlaquetteCost
      cost (scale budget) configuration plaquette
largePlaquettePaysWilsonBadCubePenalty
    {largeField = largeField} {cost = cost}
    budget configuration plaquette large =
  Wilson.largePlaquetteImpliesWilsonCost cost
    (scale budget) configuration plaquette large

finiteBadCubeWilsonBudget :
  ∀ {Scale Configuration Gauge Block Plaquette}
    {largeField : Wilson.LiteralWilsonLargeFieldData
      Scale Configuration Gauge Block Plaquette}
    {cost : Wilson.LiteralWilsonCostData largeField}
    (budget : WilsonPlaquetteBadCubeBudget largeField cost)
    badCubeCount →
  LargeField.LessEqual (LargeField.algebra (asLargeFieldCubeBudget budget))
    (LargeField.natScale
      (LargeField.algebra (asLargeFieldCubeBudget budget))
      (LargeField.add
        (LargeField.algebra (asLargeFieldCubeBudget budget))
        (entropyPerBadCube budget)
        (reservedSlackPerBadCube budget))
      badCubeCount)
    (LargeField.natScale
      (LargeField.algebra (asLargeFieldCubeBudget budget))
      (wilsonPenaltyPerBadCube budget)
      badCubeCount)
finiteBadCubeWilsonBudget budget =
  LargeField.largeFieldPenaltyPaysFiniteEntropyAndSlack
    (asLargeFieldCubeBudget budget)

wilsonPlaquetteBadCubePenaltyLevel : ProofLevel
wilsonPlaquetteBadCubePenaltyLevel = machineChecked

wilsonFiniteBadRegionBudgetLevel : ProofLevel
wilsonFiniteBadRegionBudgetLevel = machineChecked

physicalWilsonEntropyComparisonInputsLevel : ProofLevel
physicalWilsonEntropyComparisonInputsLevel = conditional
