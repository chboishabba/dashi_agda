module DASHI.Physics.Closure.NSTriadKNGalerkinGlobalRegularityCompletion where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Exact completion obligations after a Stage-3 estimate.
--
-- This module prevents the spectral theorem from being confused with the
-- Millennium endpoint.  Every quantifier needed to pass from finite Galerkin
-- systems to an arbitrary-data global smooth solution is carried explicitly.
------------------------------------------------------------------------

record GalerkinGlobalCompletion
    {i c t g l s : Level}
    (InitialData : Set i)
    (Cutoff : Set c)
    (Time : Set t)
    (GalerkinState : Set g)
    (LimitState : Set l)
    (Scalar : Set s) :
    Set (lsuc (i ⊔ c ⊔ t ⊔ g ⊔ l ⊔ s)) where
  field
    AdmissibleInitialData : InitialData → Set i
    SmoothInitialData : InitialData → Set i
    DivergenceFreeInitialData : InitialData → Set i

    galerkins : InitialData → Cutoff → Time → GalerkinState

    GalerkinSolvesProjectedNS :
      InitialData → Cutoff → (Time → GalerkinState) → Set (t ⊔ g)
    galerkinsSolveProjectedNS :
      ∀ u0 N → AdmissibleInitialData u0 →
      GalerkinSolvesProjectedNS u0 N (galerkins u0 N)

    strongNormSquared dissipation :
      Cutoff → Time → GalerkinState → Scalar

    UniformAprioriEstimate :
      InitialData → Set (i ⊔ c ⊔ t ⊔ g ⊔ s)

    stage3GapProducesUniformApriori :
      ∀ u0 →
      AdmissibleInitialData u0 →
      SmoothInitialData u0 →
      DivergenceFreeInitialData u0 →
      UniformAprioriEstimate u0

    selectedSubsequence : InitialData → Cutoff → Cutoff
    limit : InitialData → Time → LimitState

    Compactness :
      InitialData → (Cutoff → Time → GalerkinState) →
      (Time → LimitState) → Set (c ⊔ t ⊔ g ⊔ l)

    uniformEstimateGivesCompactness :
      ∀ u0 →
      UniformAprioriEstimate u0 →
      Compactness u0
        (λ N time → galerkins u0 (selectedSubsequence u0 N) time)
        (limit u0)

    SolvesNavierStokes :
      InitialData → (Time → LimitState) → Set (i ⊔ t ⊔ l)

    nonlinearTermPassesToLimit :
      ∀ u0 →
      AdmissibleInitialData u0 →
      Compactness u0
        (λ N time → galerkins u0 (selectedSubsequence u0 N) time)
        (limit u0) →
      SolvesNavierStokes u0 (limit u0)

    RecoversInitialData :
      InitialData → (Time → LimitState) → Set (i ⊔ t ⊔ l)

    limitRecoversInitialData :
      ∀ u0 →
      AdmissibleInitialData u0 →
      UniformAprioriEstimate u0 →
      RecoversInitialData u0 (limit u0)

    SmoothSolution :
      InitialData → (Time → LimitState) → Set (i ⊔ t ⊔ l)

    aprioriEstimateBootstrapsSmoothness :
      ∀ u0 →
      SmoothInitialData u0 →
      SolvesNavierStokes u0 (limit u0) →
      UniformAprioriEstimate u0 →
      SmoothSolution u0 (limit u0)

    UniqueSolution :
      InitialData → (Time → LimitState) → Set (i ⊔ t ⊔ l)

    smoothSolutionUnique :
      ∀ u0 →
      SmoothSolution u0 (limit u0) →
      SolvesNavierStokes u0 (limit u0) →
      UniqueSolution u0 (limit u0)

    GlobalInTime :
      (Time → LimitState) → Set (t ⊔ l)

    continuationForAllTime :
      ∀ u0 →
      UniformAprioriEstimate u0 →
      SmoothSolution u0 (limit u0) →
      GlobalInTime (limit u0)

open GalerkinGlobalCompletion public

record ClayPeriodicExistenceAndSmoothness
    {i t l : Level}
    (InitialData : Set i)
    (Time : Set t)
    (LimitState : Set l) :
    Set (lsuc (i ⊔ t ⊔ l)) where
  constructor clay-periodic-existence-and-smoothness
  field
    Admissible Smooth DivergenceFree : InitialData → Set i
    solution : InitialData → Time → LimitState
    SolvesNS RecoversData SmoothForAllTime Unique :
      InitialData → (Time → LimitState) → Set (i ⊔ t ⊔ l)

    arbitraryDataEndpoint :
      ∀ u0 →
      Admissible u0 →
      Smooth u0 →
      DivergenceFree u0 →
      SolvesNS u0 (solution u0)

    recoversInitialData :
      ∀ u0 →
      Admissible u0 →
      Smooth u0 →
      DivergenceFree u0 →
      RecoversData u0 (solution u0)

    globallySmooth :
      ∀ u0 →
      Admissible u0 →
      Smooth u0 →
      DivergenceFree u0 →
      SmoothForAllTime u0 (solution u0)

    unique :
      ∀ u0 →
      Admissible u0 →
      Smooth u0 →
      DivergenceFree u0 →
      Unique u0 (solution u0)

open ClayPeriodicExistenceAndSmoothness public

galerkinCompletionCutsetImplemented : Bool
galerkinCompletionCutsetImplemented = true

galerkinCompletionCutsetImplementedIsTrue :
  galerkinCompletionCutsetImplemented ≡ true
galerkinCompletionCutsetImplementedIsTrue = refl

stage3GapToUniformAprioriClosed : Bool
stage3GapToUniformAprioriClosed = false

stage3GapToUniformAprioriClosedIsFalse :
  stage3GapToUniformAprioriClosed ≡ false
stage3GapToUniformAprioriClosedIsFalse = refl

arbitraryDataGlobalRegularityClosed : Bool
arbitraryDataGlobalRegularityClosed = false

arbitraryDataGlobalRegularityClosedIsFalse :
  arbitraryDataGlobalRegularityClosed ≡ false
arbitraryDataGlobalRegularityClosedIsFalse = refl
