module DASHI.Physics.Closure.NSPeriodicCutoffUniformContinuumBKMCompletion where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Sigma using (Σ; _,_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Final finite-cutoff-to-continuum completion surface.
--
-- This module begins only after all-data adaptive coverage has supplied a
-- cutoff-uniform finite-vorticity expenditure.  It names compactness, equation
-- passage, lower-semicontinuity/limit transport, BKM continuation, and arbitrary
-- time iteration separately, then assembles the global endpoint.
------------------------------------------------------------------------

record PeriodicCutoffUniformContinuumInputs
    {i : Level}
    (Cutoff InitialDatum GalerkinSolution ContinuumSolution Time : Set i) :
    Set (lsuc i) where
  field
    SmoothDivergenceFreeMeanZero : InitialDatum → Set i

    GalerkinSolvesFrom :
      Cutoff → InitialDatum → GalerkinSolution → Set i

    ContinuumSolvesFrom :
      InitialDatum → ContinuumSolution → Set i

    CutoffVorticityIntegralFinite :
      Cutoff → GalerkinSolution → Time → Set i

    ContinuumVorticityIntegralFinite :
      ContinuumSolution → Time → Set i

    ContinuesBeyond : InitialDatum → Time → Set i
    GlobalSmoothSolution : InitialDatum → Set i

    allDataCoverageAtEveryCutoff : ∀ N u₀ uN T →
      SmoothDivergenceFreeMeanZero u₀ →
      GalerkinSolvesFrom N u₀ uN →
      CutoffVorticityIntegralFinite N uN T

    CutoffUniformBound : InitialDatum → Time → Set i

    cutoffUniformity : ∀ N u₀ uN T →
      SmoothDivergenceFreeMeanZero u₀ →
      GalerkinSolvesFrom N u₀ uN →
      CutoffVorticityIntegralFinite N uN T →
      CutoffUniformBound u₀ T

    SelectedGalerkinFamily : InitialDatum → Set i
    selectedGalerkinFamily : ∀ u₀ →
      SmoothDivergenceFreeMeanZero u₀ →
      SelectedGalerkinFamily u₀

    CompactSubsequence : InitialDatum → Set i
    compactnessExtraction : ∀ u₀ →
      SmoothDivergenceFreeMeanZero u₀ →
      SelectedGalerkinFamily u₀ →
      CompactSubsequence u₀

    limitSolution :
      (u₀ : InitialDatum) →
      CompactSubsequence u₀ →
      ContinuumSolution

    limitPreservesNavierStokes :
      ∀ u₀
        (smooth : SmoothDivergenceFreeMeanZero u₀)
        (subsequence : CompactSubsequence u₀) →
      ContinuumSolvesFrom u₀ (limitSolution u₀ subsequence)

    vorticityBoundPassesToLimit :
      ∀ u₀ T
        (subsequence : CompactSubsequence u₀) →
      SmoothDivergenceFreeMeanZero u₀ →
      CutoffUniformBound u₀ T →
      ContinuumVorticityIntegralFinite
        (limitSolution u₀ subsequence) T

    bkmContinuation : ∀ u₀ u T →
      SmoothDivergenceFreeMeanZero u₀ →
      ContinuumSolvesFrom u₀ u →
      ContinuumVorticityIntegralFinite u T →
      ContinuesBeyond u₀ T

    arbitraryFiniteTimeContinuationImpliesGlobal : ∀ u₀ →
      SmoothDivergenceFreeMeanZero u₀ →
      (∀ T → ContinuesBeyond u₀ T) →
      GlobalSmoothSolution u₀

open PeriodicCutoffUniformContinuumInputs public

periodicContinuumSolutionAndEquation :
  ∀ {i} {Cutoff InitialDatum GalerkinSolution ContinuumSolution Time : Set i} →
  (C : PeriodicCutoffUniformContinuumInputs
    Cutoff InitialDatum GalerkinSolution ContinuumSolution Time) →
  ∀ u₀ →
  SmoothDivergenceFreeMeanZero C u₀ →
  Σ ContinuumSolution (λ u → ContinuumSolvesFrom C u₀ u)
periodicContinuumSolutionAndEquation C u₀ smooth =
  limitSolution C u₀ subsequence ,
  limitPreservesNavierStokes C u₀ smooth subsequence
  where
  family : SelectedGalerkinFamily C u₀
  family = selectedGalerkinFamily C u₀ smooth

  subsequence : CompactSubsequence C u₀
  subsequence = compactnessExtraction C u₀ smooth family

periodicContinuumGlobalRegularity :
  ∀ {i} {Cutoff InitialDatum GalerkinSolution ContinuumSolution Time : Set i} →
  (C : PeriodicCutoffUniformContinuumInputs
    Cutoff InitialDatum GalerkinSolution ContinuumSolution Time) →
  (selectedCutoff : Time → Cutoff) →
  (selectedGalerkinSolution : Time → GalerkinSolution) →
  ∀ u₀ →
  SmoothDivergenceFreeMeanZero C u₀ →
  (∀ T → GalerkinSolvesFrom C
    (selectedCutoff T) u₀ (selectedGalerkinSolution T)) →
  GlobalSmoothSolution C u₀
periodicContinuumGlobalRegularity C selectedCutoff selectedGalerkinSolution u₀ smooth solves =
  arbitraryFiniteTimeContinuationImpliesGlobal C u₀ smooth continuationAtEveryTime
  where
  family : SelectedGalerkinFamily C u₀
  family = selectedGalerkinFamily C u₀ smooth

  subsequence : CompactSubsequence C u₀
  subsequence = compactnessExtraction C u₀ smooth family

  continuum : ContinuumSolution
  continuum = limitSolution C u₀ subsequence

  continuumSolves : ContinuumSolvesFrom C u₀ continuum
  continuumSolves = limitPreservesNavierStokes C u₀ smooth subsequence

  continuationAtEveryTime : ∀ T → ContinuesBeyond C u₀ T
  continuationAtEveryTime T =
    bkmContinuation C u₀ continuum T smooth continuumSolves continuumBKM
    where
    cutoffBKM :
      CutoffVorticityIntegralFinite C
        (selectedCutoff T) (selectedGalerkinSolution T) T
    cutoffBKM =
      allDataCoverageAtEveryCutoff C
        (selectedCutoff T) u₀ (selectedGalerkinSolution T) T
        smooth (solves T)

    uniform : CutoffUniformBound C u₀ T
    uniform =
      cutoffUniformity C
        (selectedCutoff T) u₀ (selectedGalerkinSolution T) T
        smooth (solves T) cutoffBKM

    continuumBKM : ContinuumVorticityIntegralFinite C continuum T
    continuumBKM =
      vorticityBoundPassesToLimit C u₀ T subsequence smooth uniform

------------------------------------------------------------------------
-- Proof-level and fail-closed status.
------------------------------------------------------------------------

cutoffToContinuumAssemblyLevel : ProofLevel
cutoffToContinuumAssemblyLevel = machineChecked

cutoffUniformVorticityEstimateLevel : ProofLevel
cutoffUniformVorticityEstimateLevel = conjectural

periodicGalerkinCompactnessLevel : ProofLevel
periodicGalerkinCompactnessLevel = standardImported

vorticityLimitTransportLevel : ProofLevel
vorticityLimitTransportLevel = conditional

periodicContinuumBKMCompletionInputsInhabited : Bool
periodicContinuumBKMCompletionInputsInhabited = false

unconditionalPeriodicGlobalRegularityPromoted : Bool
unconditionalPeriodicGlobalRegularityPromoted = false
