module DASHI.Physics.Closure.NSTriadKNGalerkinCompletionEndpoint where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.NSTriadKNGalerkinGlobalRegularityCompletion as Global

module _
    {i c t g l s : Level}
    {InitialData : Set i}
    {Cutoff : Set c}
    {Time : Set t}
    {GalerkinState : Set g}
    {LimitState : Set l}
    {Scalar : Set s}
    (completion :
      Global.GalerkinGlobalCompletion
        InitialData Cutoff Time GalerkinState LimitState Scalar)
    where

  open Global.GalerkinGlobalCompletion completion

  uniformFor :
    (u0 : InitialData) →
    AdmissibleInitialData u0 →
    SmoothInitialData u0 →
    DivergenceFreeInitialData u0 →
    UniformAprioriEstimate u0
  uniformFor u0 admissible smooth divergenceFree =
    stage3GapProducesUniformApriori
      u0 admissible smooth divergenceFree

  compactFor :
    (u0 : InitialData) →
    AdmissibleInitialData u0 →
    SmoothInitialData u0 →
    DivergenceFreeInitialData u0 →
    Compactness u0
      (λ N time → galerkins u0 (selectedSubsequence u0 N) time)
      (limit u0)
  compactFor u0 admissible smooth divergenceFree =
    uniformEstimateGivesCompactness u0
      (uniformFor u0 admissible smooth divergenceFree)

  solvesFor :
    (u0 : InitialData) →
    AdmissibleInitialData u0 →
    SmoothInitialData u0 →
    DivergenceFreeInitialData u0 →
    SolvesNavierStokes u0 (limit u0)
  solvesFor u0 admissible smooth divergenceFree =
    nonlinearTermPassesToLimit
      u0 admissible
      (compactFor u0 admissible smooth divergenceFree)

  recoversFor :
    (u0 : InitialData) →
    AdmissibleInitialData u0 →
    SmoothInitialData u0 →
    DivergenceFreeInitialData u0 →
    RecoversInitialData u0 (limit u0)
  recoversFor u0 admissible smooth divergenceFree =
    limitRecoversInitialData
      u0 admissible
      (uniformFor u0 admissible smooth divergenceFree)

  smoothFor :
    (u0 : InitialData) →
    AdmissibleInitialData u0 →
    SmoothInitialData u0 →
    DivergenceFreeInitialData u0 →
    SmoothSolution u0 (limit u0)
  smoothFor u0 admissible smooth divergenceFree =
    aprioriEstimateBootstrapsSmoothness
      u0 smooth
      (solvesFor u0 admissible smooth divergenceFree)
      (uniformFor u0 admissible smooth divergenceFree)

  globalFor :
    (u0 : InitialData) →
    AdmissibleInitialData u0 →
    SmoothInitialData u0 →
    DivergenceFreeInitialData u0 →
    GlobalInTime (limit u0)
  globalFor u0 admissible smooth divergenceFree =
    continuationForAllTime
      u0
      (uniformFor u0 admissible smooth divergenceFree)
      (smoothFor u0 admissible smooth divergenceFree)

  uniqueFor :
    (u0 : InitialData) →
    AdmissibleInitialData u0 →
    SmoothInitialData u0 →
    DivergenceFreeInitialData u0 →
    UniqueSolution u0 (limit u0)
  uniqueFor u0 admissible smooth divergenceFree =
    smoothSolutionUnique
      u0
      (smoothFor u0 admissible smooth divergenceFree)
      (solvesFor u0 admissible smooth divergenceFree)

  galerkinCompletionImpliesClayPeriodic :
    Global.ClayPeriodicExistenceAndSmoothness
      InitialData Time LimitState
  galerkinCompletionImpliesClayPeriodic = record
    { Admissible = AdmissibleInitialData
    ; Smooth = SmoothInitialData
    ; DivergenceFree = DivergenceFreeInitialData
    ; solution = limit
    ; SolvesNS = SolvesNavierStokes
    ; RecoversData = RecoversInitialData
    ; SmoothForAllTime = λ u0 candidate →
        SmoothSolution u0 candidate × GlobalInTime candidate
    ; Unique = UniqueSolution
    ; arbitraryDataEndpoint = solvesFor
    ; recoversInitialData = recoversFor
    ; globallySmooth = λ u0 admissible smooth divergenceFree →
        smoothFor u0 admissible smooth divergenceFree ,
        globalFor u0 admissible smooth divergenceFree
    ; unique = uniqueFor
    }

galerkinToClayEndpointCompositionClosed : Bool
galerkinToClayEndpointCompositionClosed = true

galerkinToClayEndpointCompositionClosedIsTrue :
  galerkinToClayEndpointCompositionClosed ≡ true
galerkinToClayEndpointCompositionClosedIsTrue = refl
