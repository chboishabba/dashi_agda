module DASHI.Physics.Closure.NSPeriodicAllDataCoverageCompletion where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; false)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

import DASHI.Physics.Closure.NSPeriodicDiffuseSpectrumBKMCompletion as Diffuse
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exhaustive all-data coverage from zero, normalized/adaptive chart, and
-- diffuse-spectrum branches.
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

    zeroDatumGlobal : ∀ u₀ T →
      ZeroDatum u₀ → ContinuesBeyond u₀ T

    chartBoundaryInvariant : ∀ u T →
      NormalizedAdaptiveChartControlled u T →
      NormalizedBoundaryInvariant u T

    chartSwitchingControlled : ∀ u T →
      NormalizedAdaptiveChartControlled u T →
      HystereticSwitchingControlled u T

    chartControlGivesBKM : ∀ u T →
      NormalizedAdaptiveChartControlled u T →
      Diffuse.VorticityTimeIntegralFinite diffuseInputs u T

    bkmContinuation : ∀ u₀ u T →
      SmoothDivergenceFreeFiniteEnergy u₀ →
      Diffuse.SolvesFrom diffuseInputs u₀ u →
      Diffuse.VorticityTimeIntegralFinite diffuseInputs u T →
      ContinuesBeyond u₀ T

open PeriodicAllDataCoverageInputs public

periodicAllDataContinuesBeyond :
  ∀ {i} {InitialDatum Solution Time State Shell : Set i} →
  (C : PeriodicAllDataCoverageInputs
    InitialDatum Solution Time State Shell) →
  ∀ u₀ u T →
  SmoothDivergenceFreeFiniteEnergy C u₀ →
  Diffuse.SolvesFrom (diffuseInputs C) u₀ u →
  ContinuesBeyond C u₀ T
periodicAllDataContinuesBeyond C u₀ u T smooth solves
  with exhaustiveClassification C u₀ u T smooth solves
... | inj₁ zero = zeroDatumGlobal C u₀ T zero
... | inj₂ (inj₁ chart) =
  bkmContinuation C u₀ u T smooth solves
    (chartControlGivesBKM C u T chart)
... | inj₂ (inj₂ diffuse) =
  bkmContinuation C u₀ u T smooth solves
    (Diffuse.periodicDiffuseSpectrumGivesBKM
      (diffuseInputs C) u₀ u T solves diffuse)

normalizedChartCarriesBothControls :
  ∀ {i} {InitialDatum Solution Time State Shell : Set i} →
  (C : PeriodicAllDataCoverageInputs
    InitialDatum Solution Time State Shell) →
  ∀ u T →
  NormalizedAdaptiveChartControlled C u T →
  NormalizedBoundaryInvariant C u T
  × HystereticSwitchingControlled C u T
normalizedChartCarriesBothControls C u T chart =
  chartBoundaryInvariant C u T chart , chartSwitchingControlled C u T chart
  where
  infixr 4 _×_
  record _×_ (A B : Set _) : Set _ where
    constructor _,_
    field first : A
          second : B

------------------------------------------------------------------------
-- Proof-level and fail-closed status.
------------------------------------------------------------------------

allDataCoverageCaseAssemblyLevel : ProofLevel
allDataCoverageCaseAssemblyLevel = machineChecked

exhaustiveZeroChartDiffuseClassificationLevel : ProofLevel
exhaustiveZeroChartDiffuseClassificationLevel = conjectural

allDataAdaptiveCoverageInputsInhabited : Bool
allDataAdaptiveCoverageInputsInhabited = false
