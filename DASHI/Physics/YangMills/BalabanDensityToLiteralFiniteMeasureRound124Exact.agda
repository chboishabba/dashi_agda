{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanDensityToLiteralFiniteMeasureRound124Exact where

------------------------------------------------------------------------
-- ROUND124: BETA-DRIVEN EFFECTIVE DENSITY IS THE LITERAL CLAY FINITE MEASURE
--
-- The literal Clay construction already owns the finite-cutoff family
-- `finiteMeasure Y G : Cutoff -> FiniteMeasure`.  The Balaban complete-density
-- flow owns `densityAt k` on the exact beta history.  A source-exact QFT recovery
-- must identify these families; otherwise stress convergence could occur on a
-- parallel density unrelated to the finite measures used by the Schwinger limit.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

record BalabanDensityLiteralFiniteMeasureWeld
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (group : Top.CompactSimpleGroup C) : Set₁ where
  field
    cutoffAtScale : Nat → Top.Cutoff C
    densityToFiniteMeasure : BetaDensity.Density inputs → Top.FiniteMeasure C

    densityAtScaleIsLiteralFiniteMeasure : ∀ scale →
      densityToFiniteMeasure (BetaDensity.densityAt inputs scale)
      ≡ Top.finiteMeasure Y group (cutoffAtScale scale)
open BalabanDensityLiteralFiniteMeasureWeld public

literalFiniteMeasureAtBalabanScale :
  ∀ {trajectory split inputs C S}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    (dataSet : BalabanDensityLiteralFiniteMeasureWeld
      {trajectory = trajectory} {split = split} {inputs = inputs}
      Y group) →
  Nat → Top.FiniteMeasure C
literalFiniteMeasureAtBalabanScale dataSet scale =
  Top.finiteMeasure _ _ (cutoffAtScale dataSet scale)

balabanDensityMapsToLiteralFiniteMeasure :
  ∀ {trajectory split inputs C S}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    (dataSet : BalabanDensityLiteralFiniteMeasureWeld
      {trajectory = trajectory} {split = split} {inputs = inputs}
      Y group) →
  ∀ scale →
  densityToFiniteMeasure dataSet (BetaDensity.densityAt inputs scale)
  ≡ literalFiniteMeasureAtBalabanScale dataSet scale
balabanDensityMapsToLiteralFiniteMeasure dataSet =
  densityAtScaleIsLiteralFiniteMeasure dataSet

balabanDensityLiteralFiniteMeasureCompilerLevel : ProofLevel
balabanDensityLiteralFiniteMeasureCompilerLevel = machineChecked

-- Physical BC1/QFT recovery seam: instantiate the measure construction and
-- cutoff map so the complete-density trajectory is literally the finite measure
-- family consumed by `IsContinuumLimitOf` in the Clay target.
literalBalabanDensityIsClayFiniteMeasureLevel : ProofLevel
literalBalabanDensityIsClayFiniteMeasureLevel = conditional
