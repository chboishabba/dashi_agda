{-# OPTIONS --safe #-}
module DASHI.Physics.Dynamics.SingularBasinResolutionWitnessExact where

open import DASHI.Core.Prelude
import DASHI.Physics.Dynamics.BasinResolutionRobustnessExact as BRR
import DASHI.Physics.Dynamics.SingularBasinFiniteWitnessExact as Finite
import DASHI.Physics.Dynamics.SingularBasinReductionExact as SBR

data Resolution : Set where
  selectedResolution : Resolution
  coarseResolution : Resolution

data Near :
  Resolution →
  Finite.FullState →
  Finite.FullState →
  Set where
  nearReflexiveSelected :
    ∀ {x} →
    Near selectedResolution x x
  funnelOutsideSelected :
    Near selectedResolution
      Finite.funnelState
      Finite.outsideState
  nearReflexiveCoarse :
    ∀ {x} →
    Near coarseResolution x x
  funnelOutsideCoarse :
    Near coarseResolution
      Finite.funnelState
      Finite.outsideState

finiteResolutionGeometry :
  BRR.ResolutionGeometry
    Finite.FullState Resolution
finiteResolutionGeometry =
  record { Near = Near }

selectedIncludedInCoarse :
  BRR.ResolutionIncludes
    finiteResolutionGeometry
    selectedResolution
    coarseResolution
selectedIncludedInCoarse =
  record
    { includes = includesSelected
    }
  where
    includesSelected :
      ∀ x y →
      Near selectedResolution x y →
      Near coarseResolution x y
    includesSelected x .x nearReflexiveSelected =
      nearReflexiveCoarse
    includesSelected
      Finite.funnelState
      Finite.outsideState
      funnelOutsideSelected =
      funnelOutsideCoarse

selected-boundary-resolution-witness :
  BRR.BasinBoundaryResolutionWitness
    finiteResolutionGeometry
    Finite.FullInBasin
    selectedResolution
selected-boundary-resolution-witness =
  record
    { inside = Finite.funnelState
    ; outside = Finite.outsideState
    ; withinResolution = funnelOutsideSelected
    ; insideHas = Finite.funnelInBasin
    ; outsideLacks = Finite.outside-not-in-full-basin
    }

funnel-state-not-robust-at-selected-resolution :
  ¬ BRR.RobustAt
      finiteResolutionGeometry
      Finite.FullInBasin
      selectedResolution
      Finite.funnelState
funnel-state-not-robust-at-selected-resolution =
  BRR.boundary-witness-refutes-robustness
    selected-boundary-resolution-witness

coarse-boundary-resolution-witness :
  BRR.BasinBoundaryResolutionWitness
    finiteResolutionGeometry
    Finite.FullInBasin
    coarseResolution
coarse-boundary-resolution-witness =
  BRR.boundary-witness-weaken
    selectedIncludedInCoarse
    selected-boundary-resolution-witness

selected-same-observation-boundary :
  BRR.SameObservationBoundaryWitness
    finiteResolutionGeometry
    Finite.project
    Finite.FullInBasin
    selectedResolution
selected-same-observation-boundary =
  record
    { inside = Finite.funnelState
    ; outside = Finite.outsideState
    ; withinResolution = funnelOutsideSelected
    ; sameObservation = refl
    ; insideHas = Finite.funnelInBasin
    ; outsideLacks = Finite.outside-not-in-full-basin
    }

selected-projection-not-resolution-adequate :
  ¬ BRR.ResolutionAdequateForPredicate
      finiteResolutionGeometry
      Finite.project
      Finite.FullInBasin
      selectedResolution
selected-projection-not-resolution-adequate =
  BRR.same-observation-boundary-refutes-resolution-adequacy
    selected-same-observation-boundary

selected-resolution-witness-also-refutes-global-factorisation :
  ¬ SBR.PredicateFactorisation
      Finite.project
      Finite.FullInBasin
selected-resolution-witness-also-refutes-global-factorisation =
  BRR.same-observation-boundary-refutes-global-factorisation
    selected-same-observation-boundary
