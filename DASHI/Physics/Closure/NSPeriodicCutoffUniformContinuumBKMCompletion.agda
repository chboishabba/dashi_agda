module DASHI.Physics.Closure.NSPeriodicCutoffUniformContinuumBKMCompletion where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Sigma using (Σ; _,_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Final finite-cutoff-to-continuum completion surface.
--
-- This module begins only after all-data adaptive coverage has supplied a
-- cutoff-uniform finite-vorticity expenditure.  All cutoff estimates,
-- compactness witnesses and the continuum limit are tied to one selected
-- Galerkin family, preventing estimates for unrelated approximations from being
-- combined in the final BKM assembly.
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

    SelectedGalerkinFamily : InitialDatum → Set i
    selectedGalerkinFamily : ∀ u₀ →
      SmoothDivergenceFreeMeanZero u₀ →
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
      SmoothDivergenceFreeMeanZero u₀ →
      GalerkinSolvesFrom N u₀ uN →
      FamilyContains family N uN →
      CutoffVorticityIntegralFinite N uN T →
      CutoffUniformBound u₀ family T

    CompactSubsequence :
      (u₀ : InitialDatum) →
      SelectedGalerkinFamily u₀ → Set i

    compactnessExtraction :
      ∀ u₀
        (smooth : SmoothDivergenceFreeMeanZero u₀)
        (family : SelectedGalerkinFamily u₀) →
      CompactSubsequence u₀ family

    limitSolution :
      (u₀ : InitialDatum) →
      (family : SelectedGalerkinFamily u₀) →
      CompactSubsequence u₀ family →
      ContinuumSolution

    limitPreservesNavierStokes :
      ∀ u₀
        (smooth : SmoothDivergenceFreeMeanZero u₀)
        (family : SelectedGalerkinFamily u₀)
        (subsequence : CompactSubsequence u₀ family) →
      ContinuumSolvesFrom u₀ (limitSolution u₀ family subsequence)

    vorticityBoundPassesToLimit :
      ∀ u₀ T
        (family : SelectedGalerkinFamily u₀)
        (subsequence : CompactSubsequence u₀ family) →
      SmoothDivergenceFreeMeanZero u₀ →
      CutoffUniformBound u₀ family T →
      ContinuumVorticityIntegralFinite
        (limitSolution u₀ family subsequence) T

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
  limitSolution C u₀ family subsequence ,
  limitPreservesNavierStokes C u₀ smooth family subsequence
  where
  family : SelectedGalerkinFamily C u₀
  family = selectedGalerkinFamily C u₀ smooth

  subsequence : CompactSubsequence C u₀ family
  subsequence = compactnessExtraction C u₀ smooth family

periodicContinuumGlobalRegularity :
  ∀ {i} {Cutoff InitialDatum GalerkinSolution ContinuumSolution Time : Set i} →
  (C : PeriodicCutoffUniformContinuumInputs
    Cutoff InitialDatum GalerkinSolution ContinuumSolution Time) →
  (selectedCutoff : Time → Cutoff) →
  (selectedGalerkinSolution : Time → GalerkinSolution) →
  ∀ u₀ →
  (smooth : SmoothDivergenceFreeMeanZero C u₀) →
  (solves : ∀ T → GalerkinSolvesFrom C
    (selectedCutoff T) u₀ (selectedGalerkinSolution T)) →
  (familyMembership : ∀ T →
    FamilyContains C
      (selectedGalerkinFamily C u₀ smooth)
      (selectedCutoff T)
      (selectedGalerkinSolution T)) →
  GlobalSmoothSolution C u₀
periodicContinuumGlobalRegularity
    C selectedCutoff selectedGalerkinSolution u₀ smooth solves familyMembership =
  arbitraryFiniteTimeContinuationImpliesGlobal C u₀ smooth continuationAtEveryTime
  where
  family : SelectedGalerkinFamily C u₀
  family = selectedGalerkinFamily C u₀ smooth

  subsequence : CompactSubsequence C u₀ family
  subsequence = compactnessExtraction C u₀ smooth family

  continuum : ContinuumSolution
  continuum = limitSolution C u₀ family subsequence

  continuumSolves : ContinuumSolvesFrom C u₀ continuum
  continuumSolves =
    limitPreservesNavierStokes C u₀ smooth family subsequence

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

    uniform : CutoffUniformBound C u₀ family T
    uniform =
      cutoffUniformity C
        u₀ family
        (selectedCutoff T) (selectedGalerkinSolution T) T
        smooth (solves T) (familyMembership T) cutoffBKM

    continuumBKM : ContinuumVorticityIntegralFinite C continuum T
    continuumBKM =
      vorticityBoundPassesToLimit C
        u₀ T family subsequence smooth uniform

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
