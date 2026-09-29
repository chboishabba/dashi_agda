{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsSourceFirstFiniteMeasureFromDensityRound525Exact where

------------------------------------------------------------------------
-- GOAL-1 A3 / ROUND525:
-- FIXED-G LITERAL FINITE FAMILY FROM THE BETA-DRIVEN DENSITY
--
-- The historical R124 weld chose a literal finite family first and then asked
-- for
--
--   densityToFiniteMeasure (rho_k) = finiteMeasure(k).
--
-- On the preferred fixed-G route choose instead:
--
--   finiteMeasure(k) := densityToFiniteMeasure (rho_k).
--
-- The equality is then refl.  The genuine physical payment is the map from the
-- source density to the selected normalized finite YM measure.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity

record DensityToFiniteMeasureSource
    {trajectory split}
    (inputs :
      BetaDensity.BetaDrivenCompleteDensityInputs
        {trajectory = trajectory} {split = split})
    (FiniteMeasure : Set) : Set₁ where
  field
    densityToFiniteMeasure :
      BetaDensity.Density inputs → FiniteMeasure

open DensityToFiniteMeasureSource public

finiteMeasureFromDensity :
  ∀ {trajectory split inputs FiniteMeasure} →
  DensityToFiniteMeasureSource
    {trajectory = trajectory} {split = split}
    inputs FiniteMeasure →
  Nat → FiniteMeasure
finiteMeasureFromDensity {inputs = inputs} source scale =
  densityToFiniteMeasure source
    (BetaDensity.densityAt inputs scale)

densityAtScaleIsChosenFiniteMeasure :
  ∀ {trajectory split inputs FiniteMeasure}
    (source :
      DensityToFiniteMeasureSource
        {trajectory = trajectory} {split = split}
        inputs FiniteMeasure)
    scale →
  densityToFiniteMeasure source
    (BetaDensity.densityAt inputs scale)
  ≡
  finiteMeasureFromDensity source scale
densityAtScaleIsChosenFiniteMeasure source scale = refl

round525SourceFirstFiniteFamilyCompilerLevel : ProofLevel
round525SourceFirstFiniteFamilyCompilerLevel = machineChecked

round525DensityFiniteFamilyEqualityLevel : ProofLevel
round525DensityFiniteFamilyEqualityLevel = machineChecked

-- Physical input still required: the literal source density must define the
-- normalized finite YM measure used downstream.
literalRound525DensityToFiniteMeasureMapLevel : ProofLevel
literalRound525DensityToFiniteMeasureMapLevel = conditional
