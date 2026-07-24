module DASHI.Physics.Closure.NSPeriodicAllDataCutoffCoverageAdapter where

open import Agda.Primitive using (Level; lsuc)

import DASHI.Physics.Closure.NSPeriodicDiffuseSpectrumBKMCompletion as Diffuse
import DASHI.Physics.Closure.NSPeriodicAllDataCoverageCompletion as Coverage

------------------------------------------------------------------------
-- Carrier-coherent bridge from the zero/chart/diffuse coverage theorem to the
-- cutoff-indexed vorticity premise required by the continuum completion.
------------------------------------------------------------------------

record AllDataCutoffCoverageAdapter
    {i : Level}
    (Cutoff InitialDatum GalerkinSolution Time State Shell : Set i) :
    Set (lsuc i) where
  field
    coverage : Coverage.PeriodicAllDataCoverageInputs
      InitialDatum GalerkinSolution Time State Shell

    SmoothDivergenceFreeMeanZero : InitialDatum → Set i
    GalerkinSolvesFrom :
      Cutoff → InitialDatum → GalerkinSolution → Set i
    CutoffVorticityIntegralFinite :
      Cutoff → GalerkinSolution → Time → Set i

    smoothImpliesCoverageDatum : ∀ u₀ →
      SmoothDivergenceFreeMeanZero u₀ →
      Coverage.SmoothDivergenceFreeFiniteEnergy coverage u₀

    cutoffSolutionImpliesCoverageSolution : ∀ N u₀ uN →
      GalerkinSolvesFrom N u₀ uN →
      Diffuse.SolvesFrom
        (Coverage.diffuseInputs coverage) u₀ uN

    coverageVorticityImpliesCutoffVorticity : ∀ N u T →
      Diffuse.VorticityTimeIntegralFinite
        (Coverage.diffuseInputs coverage) u T →
      CutoffVorticityIntegralFinite N u T

open AllDataCutoffCoverageAdapter public

allDataCoverageAtCutoff :
  ∀ {i} {Cutoff InitialDatum GalerkinSolution Time State Shell : Set i} →
  (C : AllDataCutoffCoverageAdapter
    Cutoff InitialDatum GalerkinSolution Time State Shell) →
  ∀ N u₀ uN T →
  SmoothDivergenceFreeMeanZero C u₀ →
  GalerkinSolvesFrom C N u₀ uN →
  CutoffVorticityIntegralFinite C N uN T
allDataCoverageAtCutoff C N u₀ uN T smooth solves =
  coverageVorticityImpliesCutoffVorticity C N uN T coverageBKM
  where
  coverageSmooth :
    Coverage.SmoothDivergenceFreeFiniteEnergy (coverage C) u₀
  coverageSmooth = smoothImpliesCoverageDatum C u₀ smooth

  coverageSolves :
    Diffuse.SolvesFrom
      (Coverage.diffuseInputs (coverage C)) u₀ uN
  coverageSolves =
    cutoffSolutionImpliesCoverageSolution C N u₀ uN solves

  coverageBKM :
    Diffuse.VorticityTimeIntegralFinite
      (Coverage.diffuseInputs (coverage C)) uN T
  coverageBKM =
    Coverage.periodicAllDataVorticityFinite
      (coverage C) u₀ uN T coverageSmooth coverageSolves
