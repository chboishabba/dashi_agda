module DASHI.Cognition.PNF.ContinuousOscillatorMemoryRefinementRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Core.RecursiveScaleTransitionExact as Scale
import DASHI.Cognition.PNF.ContinuousOscillatorMemoryRefinementExact as Osc

------------------------------------------------------------------------
-- Recursive scale transition surface.
------------------------------------------------------------------------

scaleTransitionSurfaceExists : Set₁
scaleTransitionSurfaceExists =
  Scale.RecursiveScaleTransition ⊤ ⊤ ⊤ ⊤ ⊤ ⊤

unitTransition : Scale.RecursiveScaleTransition ⊤ ⊤ ⊤ ⊤ ⊤ ⊤
unitTransition = record
  { dynamics = λ _ → tt
  ; classifyPersistent = λ _ → tt
  ; persistentRole = λ _ → Scale.invariantSet
  ; RealisesNext = λ _ _ → ⊤
  ; realiseNextObject = λ _ → tt , tt
  }

unitLower : Scale.SituatedLowerState ⊤ ⊤ ⊤
unitLower = Scale.situatedLowerState tt tt tt

unitTransitionWitness : Scale.ScaleTransitionWitness unitTransition unitLower
unitTransitionWitness =
  Scale.scaleTransitionWitness tt refl tt refl tt tt

witnessMediatedRealisation :
  Scale.RealisesNext unitTransition
    (Scale.classifyPersistent unitTransition
      (Scale.dynamics unitTransition unitLower))
    tt
witnessMediatedRealisation = tt

nonAttractorPersistenceSurface : Scale.PersistentRole
nonAttractorPersistenceSurface = Scale.persistenceNeedNotBeAttractor

------------------------------------------------------------------------
-- Continuous oscillator refinement surface.
------------------------------------------------------------------------

oscillatorSchemaSurfaceExists : Set₁
oscillatorSchemaSurfaceExists = Osc.OscillatorSchema

continuousBoundarySurfaceExists : Set₁
continuousBoundarySurfaceExists = Osc.ContinuousOscillatorBoundary
