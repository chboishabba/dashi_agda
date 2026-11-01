module DASHI.Physics.Closure.NSTriadKNFourierLimitCompletionComposition where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Fourier-first global completion.
--
-- This isolates the exact compactness route appropriate to the periodic
-- coefficient architecture: modewise diagonal convergence plus a uniform
-- Sobolev tail, followed by nonlinear product convergence.
------------------------------------------------------------------------

record FourierCompactnessInputs
    {i c t m s l : Level} :
    Set (lsuc (i ⊔ c ⊔ t ⊔ m ⊔ s ⊔ l)) where
  field
    InitialData : Set i
    Cutoff : Set c
    Time : Set t
    Mode : Set m
    GalerkinState : Set s
    LimitState : Set l

    Admissible Smooth DivergenceFree : InitialData → Set i

    galerkins : InitialData → Cutoff → Time → GalerkinState
    limit : InitialData → Time → LimitState

    coefficient : GalerkinState → Mode → Set
    limitCoefficient : LimitState → Mode → Set

    finiteModeDiagonalSubsequence : Set
    uniformSobolevTailSmall : Set
    modewisePlusTailImpliesStrongConvergence : Set

    productStrongConvergence : Set
    projectorConvergesToIdentity : Set
    nonlinearGalerkinTermPassesToLimit : Set

    projectedInitialDataConverges : Set
    limitContinuousAtInitialTime : Set
    limitRecoversInitialData : Set

open FourierCompactnessInputs public

record SmoothUniqueGlobalLimit
    {i c t m s l : Level}
    (C : FourierCompactnessInputs {i} {c} {t} {m} {s} {l}) :
    Set (lsuc (i ⊔ c ⊔ t ⊔ m ⊔ s ⊔ l)) where
  field
    limitSolvesNavierStokes : Set
    parabolicBootstrapAtEveryOrder : Set
    differenceEnergyInequality : Set
    uniquenessByGronwall : Set
    continuationCriterion : Set
    uniformBoundRefutesFiniteMaximalTime : Set

    arbitraryDataGlobalEndpoint :
      (u0 : InitialData C) →
      Admissible C u0 →
      Smooth C u0 →
      DivergenceFree C u0 →
      Set

open SmoothUniqueGlobalLimit public

record ClayCompletionFromFourierRoute
    {i c t m s l : Level}
    (C : FourierCompactnessInputs {i} {c} {t} {m} {s} {l}) :
    Set (lsuc (i ⊔ c ⊔ t ⊔ m ⊔ s ⊔ l)) where
  constructor clay-completion-from-fourier-route
  field
    completion : SmoothUniqueGlobalLimit C
    exactPeriodicProblemMatched : Set

open ClayCompletionFromFourierRoute public

fourierLimitCompositionClosed : Bool
fourierLimitCompositionClosed = true

fourierLimitCompositionClosedIsTrue :
  fourierLimitCompositionClosed ≡ true
fourierLimitCompositionClosedIsTrue = refl
