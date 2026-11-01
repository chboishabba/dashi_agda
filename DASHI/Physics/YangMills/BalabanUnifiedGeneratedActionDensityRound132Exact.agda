{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact where

------------------------------------------------------------------------
-- ROUND132: ONE GENERATED ACTION / DENSITY FOR BC1, BC2 AND STRESS
--
-- The frozen A/BC compiler and the later stress/Schwinger lane are now both on
-- master, but they enter through different carriers:
--
--   * BC1/BC2 consume the literal CMP109/CMP116 effective potential;
--   * the stress lane consumes `densityAt k` of the beta-driven CMP122 flow.
--
-- These carriers must not be identified by type.  The physical same-action
-- theorem is instead an explicit representation map from the literal density
-- to an effective potential, together with equality to the exact BC1 carrier
-- potential at the corresponding source scale.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source

record UnifiedGeneratedActionDensity
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {History Cell : Set} {cutoff : Nat}
    (present : Present.PresentCutPhysicalSourceInputs History Cell cutoff) : Set₁ where
  field
    -- The source-scale correspondence is explicit.  It cannot depend on the
    -- background, so one fixed RG scale cannot silently become different
    -- densities for different field configurations.
    sourceScaleToDensityIndex :
      Source.Scale (Carrier.source (Present.bc1Carrier present)) → Nat

    -- Distinct carriers are preserved: a finite density is represented as an
    -- effective-potential function on the exact BC1 background carrier.
    effectivePotentialOfDensity :
      BetaDensity.Density inputs →
      Source.Background (Carrier.source (Present.bc1Carrier present)) → ℝ

    -- The decisive same-action equality.  At the BC1 source scale, the
    -- beta-driven density represents the exact potential whose CMP109/CMP116
    -- Hessian is consumed by BC1 and whose heat flow is consumed by BC2.
    selectedDensityRepresentsBC1EffectivePotential :
      ∀ background →
      effectivePotentialOfDensity
        (BetaDensity.densityAt inputs
          (sourceScaleToDensityIndex
            (Carrier.scale (Present.bc1Carrier present))))
        background
      ≡ Carrier.effectivePotential (Present.bc1Carrier present) background

open UnifiedGeneratedActionDensity public

selectedDensityIndex :
  ∀ {trajectory split inputs History Cell cutoff}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff} →
  UnifiedGeneratedActionDensity
    {trajectory = trajectory} {split = split} {inputs = inputs} present → Nat
selectedDensityIndex {present = present} weld =
  sourceScaleToDensityIndex weld (Carrier.scale (Present.bc1Carrier present))

selectedDensityRepresentsExactBC1Potential :
  ∀ {trajectory split inputs History Cell cutoff}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff}
    (weld : UnifiedGeneratedActionDensity
      {trajectory = trajectory} {split = split} {inputs = inputs} present) →
  ∀ background →
  effectivePotentialOfDensity weld
    (BetaDensity.densityAt inputs (selectedDensityIndex weld)) background
  ≡ Carrier.effectivePotential (Present.bc1Carrier present) background
selectedDensityRepresentsExactBC1Potential = selectedDensityRepresentsBC1EffectivePotential

-- BC2 is already indexed by the exact BC1 carrier.  Therefore the equality
-- above simultaneously identifies the selected beta-driven density with the
-- potential used by the compact-group Heat/Doob calculus; no second BC2
-- "same density" equality is required.
selectedDensityRepresentsBC2InitialPotential :
  ∀ {trajectory split inputs History Cell cutoff}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff}
    (weld : UnifiedGeneratedActionDensity
      {trajectory = trajectory} {split = split} {inputs = inputs} present) →
  ∀ background →
  effectivePotentialOfDensity weld
    (BetaDensity.densityAt inputs (selectedDensityIndex weld)) background
  ≡ Carrier.effectivePotential (Present.bc1Carrier present) background
selectedDensityRepresentsBC2InitialPotential = selectedDensityRepresentsExactBC1Potential

unifiedGeneratedActionDensityCompilerLevel : ProofLevel
unifiedGeneratedActionDensityCompilerLevel = machineChecked

-- Physical source seam: instantiate the representation map on the literal
-- Balaban generated density.  The equality itself is not obtained from the fact
-- that both objects are called an effective action.
literalUnifiedGeneratedActionDensityLevel : ProofLevel
literalUnifiedGeneratedActionDensityLevel = conditional
