module DASHI.Physics.Closure.NSPeriodicCutoffUniformContinuumAssembly where

open import Agda.Primitive using (Level; lsuc)

import DASHI.Physics.Closure.NSPeriodicAllDataCutoffCoverageAdapter as Coverage
import DASHI.Physics.Closure.NSPeriodicCutoffUniformContinuumBKMCompletion as Final

------------------------------------------------------------------------
-- Exact constructor connecting the all-data zero/chart/diffuse theorem at every
-- Galerkin cutoff to the final family-coherent compactness/BKM package.
------------------------------------------------------------------------

record PeriodicCutoffContinuumAssemblyInputs
    {i : Level}
    (Cutoff InitialDatum GalerkinSolution ContinuumSolution Time State Shell :
      Set i) : Set (lsuc i) where
  field
    cutoffCoverage : Coverage.AllDataCutoffCoverageAdapter
      Cutoff InitialDatum GalerkinSolution Time State Shell

    ContinuumSolvesFrom :
      InitialDatum → ContinuumSolution → Set i
    ContinuumVorticityIntegralFinite :
      ContinuumSolution → Time → Set i

    ContinuesBeyond : InitialDatum → Time → Set i
    GlobalSmoothSolution : InitialDatum → Set i

    SelectedGalerkinFamily : InitialDatum → Set i
    selectedGalerkinFamily : ∀ u₀ →
      Coverage.SmoothDivergenceFreeMeanZero cutoffCoverage u₀ →
      SelectedGalerkinFamily u₀

    FamilyContains : ∀ {u₀} →
      SelectedGalerkinFamily u₀ →
      Cutoff → GalerkinSolution → Set i

    CutoffUniformBound :
      (u₀ : InitialDatum) →
      SelectedGalerkinFamily u₀ →
      Time → Set i

    cutoffUniformity :
      ∀ u₀
        (family : SelectedGalerkinFamily u₀)
        N uN T →
      Coverage.SmoothDivergenceFreeMeanZero cutoffCoverage u₀ →
      Coverage.GalerkinSolvesFrom cutoffCoverage N u₀ uN →
      FamilyContains family N uN →
      Coverage.CutoffVorticityIntegralFinite cutoffCoverage N uN T →
      CutoffUniformBound u₀ family T

    CompactSubsequence :
      (u₀ : InitialDatum) →
      SelectedGalerkinFamily u₀ → Set i

    compactnessExtraction :
      ∀ u₀
        (smooth : Coverage.SmoothDivergenceFreeMeanZero cutoffCoverage u₀)
        (family : SelectedGalerkinFamily u₀) →
      CompactSubsequence u₀ family

    limitSolution :
      (u₀ : InitialDatum) →
      (family : SelectedGalerkinFamily u₀) →
      CompactSubsequence u₀ family →
      ContinuumSolution

    limitPreservesNavierStokes :
      ∀ u₀
        (smooth : Coverage.SmoothDivergenceFreeMeanZero cutoffCoverage u₀)
        (family : SelectedGalerkinFamily u₀)
        (subsequence : CompactSubsequence u₀ family) →
      ContinuumSolvesFrom u₀ (limitSolution u₀ family subsequence)

    vorticityBoundPassesToLimit :
      ∀ u₀ T
        (family : SelectedGalerkinFamily u₀)
        (subsequence : CompactSubsequence u₀ family) →
      Coverage.SmoothDivergenceFreeMeanZero cutoffCoverage u₀ →
      CutoffUniformBound u₀ family T →
      ContinuumVorticityIntegralFinite
        (limitSolution u₀ family subsequence) T

    bkmContinuation : ∀ u₀ u T →
      Coverage.SmoothDivergenceFreeMeanZero cutoffCoverage u₀ →
      ContinuumSolvesFrom u₀ u →
      ContinuumVorticityIntegralFinite u T →
      ContinuesBeyond u₀ T

    arbitraryFiniteTimeContinuationImpliesGlobal : ∀ u₀ →
      Coverage.SmoothDivergenceFreeMeanZero cutoffCoverage u₀ →
      (∀ T → ContinuesBeyond u₀ T) →
      GlobalSmoothSolution u₀

open PeriodicCutoffContinuumAssemblyInputs public

assemblePeriodicCutoffUniformContinuumInputs :
  ∀ {i}
    {Cutoff InitialDatum GalerkinSolution ContinuumSolution Time State Shell :
      Set i} →
  PeriodicCutoffContinuumAssemblyInputs
    Cutoff InitialDatum GalerkinSolution ContinuumSolution Time State Shell →
  Final.PeriodicCutoffUniformContinuumInputs
    Cutoff InitialDatum GalerkinSolution ContinuumSolution Time
assemblePeriodicCutoffUniformContinuumInputs I = record
  { SmoothDivergenceFreeMeanZero =
      Coverage.SmoothDivergenceFreeMeanZero (cutoffCoverage I)
  ; GalerkinSolvesFrom =
      Coverage.GalerkinSolvesFrom (cutoffCoverage I)
  ; ContinuumSolvesFrom = ContinuumSolvesFrom I
  ; CutoffVorticityIntegralFinite =
      Coverage.CutoffVorticityIntegralFinite (cutoffCoverage I)
  ; ContinuumVorticityIntegralFinite =
      ContinuumVorticityIntegralFinite I
  ; ContinuesBeyond = ContinuesBeyond I
  ; GlobalSmoothSolution = GlobalSmoothSolution I
  ; allDataCoverageAtEveryCutoff =
      Coverage.allDataCoverageAtCutoff (cutoffCoverage I)
  ; SelectedGalerkinFamily = SelectedGalerkinFamily I
  ; selectedGalerkinFamily = selectedGalerkinFamily I
  ; FamilyContains = FamilyContains I
  ; CutoffUniformBound = CutoffUniformBound I
  ; cutoffUniformity = cutoffUniformity I
  ; CompactSubsequence = CompactSubsequence I
  ; compactnessExtraction = compactnessExtraction I
  ; limitSolution = limitSolution I
  ; limitPreservesNavierStokes = limitPreservesNavierStokes I
  ; vorticityBoundPassesToLimit = vorticityBoundPassesToLimit I
  ; bkmContinuation = bkmContinuation I
  ; arbitraryFiniteTimeContinuationImpliesGlobal =
      arbitraryFiniteTimeContinuationImpliesGlobal I
  }

assembledPeriodicContinuumGlobalRegularity :
  ∀ {i}
    {Cutoff InitialDatum GalerkinSolution ContinuumSolution Time State Shell :
      Set i} →
  (I : PeriodicCutoffContinuumAssemblyInputs
    Cutoff InitialDatum GalerkinSolution ContinuumSolution Time State Shell) →
  (selectedCutoff : Time → Cutoff) →
  (selectedGalerkinSolution : Time → GalerkinSolution) →
  ∀ u₀ →
  (smooth : Coverage.SmoothDivergenceFreeMeanZero (cutoffCoverage I) u₀) →
  (solves : ∀ T →
    Coverage.GalerkinSolvesFrom
      (cutoffCoverage I)
      (selectedCutoff T) u₀ (selectedGalerkinSolution T)) →
  (familyMembership : ∀ T →
    FamilyContains I
      (selectedGalerkinFamily I u₀ smooth)
      (selectedCutoff T)
      (selectedGalerkinSolution T)) →
  GlobalSmoothSolution I u₀
assembledPeriodicContinuumGlobalRegularity
    I selectedCutoff selectedGalerkinSolution u₀ smooth solves familyMembership =
  Final.periodicContinuumGlobalRegularity
    (assemblePeriodicCutoffUniformContinuumInputs I)
    selectedCutoff selectedGalerkinSolution u₀ smooth solves familyMembership
