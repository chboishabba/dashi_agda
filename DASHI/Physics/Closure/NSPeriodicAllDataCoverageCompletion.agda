module DASHI.Physics.Closure.NSPeriodicAllDataCoverageCompletion where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

import DASHI.Physics.Closure.NSPeriodicDiffuseSpectrumBKMCompletion as Diffuse
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exhaustive all-data coverage from zero, normalized/adaptive chart, and
-- diffuse-spectrum branches.
--
-- The chart route cannot bypass its two analytic ingredients: its BKM estimate
-- is obtained only after both normalized boundary invariance and hysteretic
-- switching control have been established for the same solution and interval.
-- The zero branch also exports vorticity finiteness, allowing the all-data result
-- to feed a cutoff-uniform compactness argument before continuation is invoked.
------------------------------------------------------------------------

record PeriodicAllDataCoverageInputs
    {i : Level}
    (InitialDatum Solution Time State Shell : Set i) : Set (lsuc i) where
  field
    diffuseInputs :
      Diffuse.PeriodicDiffuseSpectrumBKMInputs
        InitialDatum Solution Time State Shell

    SmoothDivergenceFreeFiniteEnergy : InitialDatum → Set i
    ZeroDatum : InitialDatum → Set i
    NormalizedAdaptiveChartControlled : Solution → Time → Set i
    ContinuesBeyond : InitialDatum → Time → Set i

    NormalizedBoundaryInvariant : Solution → Time → Set i
    HystereticSwitchingControlled : Solution → Time → Set i

    exhaustiveClassification : ∀ u₀ u T →
      SmoothDivergenceFreeFiniteEnergy u₀ →
      Diffuse.SolvesFrom diffuseInputs u₀ u →
      ZeroDatum u₀
      ⊎ (NormalizedAdaptiveChartControlled u T
      ⊎ Diffuse.DiffuseAt diffuseInputs u T)

    zeroDatumGivesBKM : ∀ u₀ u T →
      ZeroDatum u₀ →
      Diffuse.SolvesFrom diffuseInputs u₀ u →
      Diffuse.VorticityTimeIntegralFinite diffuseInputs u T

    zeroDatumGlobal : ∀ u₀ T →
      ZeroDatum u₀ → ContinuesBeyond u₀ T

    chartBoundaryInvariant : ∀ u T →
      NormalizedAdaptiveChartControlled u T →
      NormalizedBoundaryInvariant u T

    chartSwitchingControlled : ∀ u T →
      NormalizedAdaptiveChartControlled u T →
      HystereticSwitchingControlled u T

    chartControlsGiveBKM : ∀ u T →
      NormalizedBoundaryInvariant u T →
      HystereticSwitchingControlled u T →
      Diffuse.VorticityTimeIntegralFinite diffuseInputs u T

    bkmContinuation : ∀ u₀ u T →
      SmoothDivergenceFreeFiniteEnergy u₀ →
      Diffuse.SolvesFrom diffuseInputs u₀ u →
      Diffuse.VorticityTimeIntegralFinite diffuseInputs u T →
      ContinuesBeyond u₀ T

open PeriodicAllDataCoverageInputs public

normalizedChartCarriesBothControls :
  ∀ {i} {InitialDatum Solution Time State Shell : Set i} →
  (C : PeriodicAllDataCoverageInputs
    InitialDatum Solution Time State Shell) →
  ∀ u T →
  NormalizedAdaptiveChartControlled C u T →
  Σ (NormalizedBoundaryInvariant C u T)
    (λ _ → HystereticSwitchingControlled C u T)
normalizedChartCarriesBothControls C u T chart =
  chartBoundaryInvariant C u T chart ,
  chartSwitchingControlled C u T chart

normalizedChartGivesBKM :
  ∀ {i} {InitialDatum Solution Time State Shell : Set i} →
  (C : PeriodicAllDataCoverageInputs
    InitialDatum Solution Time State Shell) →
  ∀ u T →
  NormalizedAdaptiveChartControlled C u T →
  Diffuse.VorticityTimeIntegralFinite (diffuseInputs C) u T
normalizedChartGivesBKM C u T chart =
  chartControlsGiveBKM C u T
    (chartBoundaryInvariant C u T chart)
    (chartSwitchingControlled C u T chart)

periodicAllDataVorticityFinite :
  ∀ {i} {InitialDatum Solution Time State Shell : Set i} →
  (C : PeriodicAllDataCoverageInputs
    InitialDatum Solution Time State Shell) →
  ∀ u₀ u T →
  SmoothDivergenceFreeFiniteEnergy C u₀ →
  Diffuse.SolvesFrom (diffuseInputs C) u₀ u →
  Diffuse.VorticityTimeIntegralFinite (diffuseInputs C) u T
periodicAllDataVorticityFinite C u₀ u T smooth solves
  with exhaustiveClassification C u₀ u T smooth solves
... | inj₁ zero = zeroDatumGivesBKM C u₀ u T zero solves
... | inj₂ (inj₁ chart) = normalizedChartGivesBKM C u T chart
... | inj₂ (inj₂ diffuse) =
  Diffuse.periodicDiffuseSpectrumGivesBKM
    (diffuseInputs C) u₀ u T solves diffuse

periodicAllDataContinuesBeyond :
  ∀ {i} {InitialDatum Solution Time State Shell : Set i} →
  (C : PeriodicAllDataCoverageInputs
    InitialDatum Solution Time State Shell) →
  ∀ u₀ u T →
  SmoothDivergenceFreeFiniteEnergy C u₀ →
  Diffuse.SolvesFrom (diffuseInputs C) u₀ u →
  ContinuesBeyond C u₀ T
periodicAllDataContinuesBeyond C u₀ u T smooth solves =
  bkmContinuation C u₀ u T smooth solves
    (periodicAllDataVorticityFinite C u₀ u T smooth solves)

------------------------------------------------------------------------
-- Proof-level and fail-closed status.
------------------------------------------------------------------------

allDataCoverageCaseAssemblyLevel : ProofLevel
allDataCoverageCaseAssemblyLevel = machineChecked

exhaustiveZeroChartDiffuseClassificationLevel : ProofLevel
exhaustiveZeroChartDiffuseClassificationLevel = conjectural

allDataAdaptiveCoverageInputsInhabited : Bool
allDataAdaptiveCoverageInputsInhabited = false
