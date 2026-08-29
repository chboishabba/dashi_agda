{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanBetaDrivenDensityToCMP109116CarrierRound108Exact where

------------------------------------------------------------------------
-- ROUND108 BC1: ACTUAL BETA-DRIVEN DENSITY -> CMP109/CMP116 SAME ACTION
--
-- `Balaban1989BetaDrivenCompleteDensityFlowExact` already removes the parallel
-- coupling-trajectory loophole: its densityAt k is carried on definitionally the
-- same coupling history as the finite beta calculation.  Here we remove the
-- analogous action loophole by defining the CMP109 potential AT SCALE k to be
-- the potential extracted from that exact `densityAt k`.
--
-- Thus the Part-I/Part-II source leaf is no longer "some effective action has a
-- CMP116 localization".  It is the evidence-bearing equality
--
--   potentialOfDensity (densityAt k)
--     = sum_X E_k,X^physical
--
-- on the literal beta-driven density family.  The common analytic radius is
-- attached to the same Nat scale and Volume carrier.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Flow
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Continue
import DASHI.Physics.YangMills.BalabanCMP116CommonAnalyticRadiusRound103Exact as Radius

record BetaDrivenLocalizedEffectiveActionFamily
    {trajectory split}
    (inputs : Flow.BetaDrivenCompleteDensityInputs {trajectory} {split}) : Set₁ where
  field
    Volume Background Tangent Component : Set

    potentialOfDensity : Flow.Density inputs → Background → ℝ

    components : Nat → Volume → List Component
    physicalLocalizedActivity :
      Nat → Volume → Component → Background → ℝ

    -- Literal CMP116 Part-II localization of the exact beta-driven density.
    densityPotentialIsLocalizedCompositeSum :
      ∀ scale volume background →
      potentialOfDensity (Flow.densityAt inputs scale) background
      ≡ Finite.sumFunctions
          (Finite.mapList
            (physicalLocalizedActivity scale volume)
            (components scale volume))
          background

    -- One source-native radius valid uniformly in scale and finite volume.
    commonRadius : Radius.CMP116CommonAnalyticRadius Nat Volume

open BetaDrivenLocalizedEffectiveActionFamily public

asCMP109116Continuation :
  ∀ {trajectory split}
    {inputs : Flow.BetaDrivenCompleteDensityInputs {trajectory} {split}} →
  BetaDrivenLocalizedEffectiveActionFamily inputs →
  Continue.CMP109116LiteralEffectiveActionContinuation
asCMP109116Continuation {inputs = inputs} dataSet = record
  { Continue.CMP109116LiteralEffectiveActionContinuation.Scale = Nat
  ; Continue.CMP109116LiteralEffectiveActionContinuation.Volume = Volume dataSet
  ; Continue.CMP109116LiteralEffectiveActionContinuation.Background = Background dataSet
  ; Continue.CMP109116LiteralEffectiveActionContinuation.Tangent = Tangent dataSet
  ; Continue.CMP109116LiteralEffectiveActionContinuation.Component = Component dataSet
  ; Continue.CMP109116LiteralEffectiveActionContinuation.components = components dataSet
  ; Continue.CMP109116LiteralEffectiveActionContinuation.cmp116PhysicalLocalizedActivity =
      physicalLocalizedActivity dataSet
  ; Continue.CMP109116LiteralEffectiveActionContinuation.cmp109EffectivePotential =
      λ scale → potentialOfDensity dataSet (Flow.densityAt inputs scale)
  ; Continue.CMP109116LiteralEffectiveActionContinuation.effectivePotentialIsLocalizedCompositeSum =
      densityPotentialIsLocalizedCompositeSum dataSet
  }

cmp109PotentialIsLiteralBetaDrivenDensityPotential :
  ∀ {trajectory split}
    {inputs : Flow.BetaDrivenCompleteDensityInputs {trajectory} {split}}
    (dataSet : BetaDrivenLocalizedEffectiveActionFamily inputs)
    scale volume background →
  Continue.cmp109EffectivePotential
    (asCMP109116Continuation dataSet) scale volume background
  ≡ potentialOfDensity dataSet (Flow.densityAt inputs scale) background
cmp109PotentialIsLiteralBetaDrivenDensityPotential dataSet scale volume background =
  Agda.Builtin.Equality.refl

round108BetaDrivenCMP109116ContinuationLevel : ProofLevel
round108BetaDrivenCMP109116ContinuationLevel = machineChecked

-- Physical BC1 leaf after this adapter: instantiate `potentialOfDensity`, the
-- CMP116 post-substitution local activities, their exact localized-sum equality,
-- and one positive common source radius on the SAME beta-driven density family.
literalBetaDrivenCMP116LocalizationAndRadiusRound108Level : ProofLevel
literalBetaDrivenCMP116LocalizationAndRadiusRound108Level = conditional
