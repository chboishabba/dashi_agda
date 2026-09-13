module DASHI.Cognition.PNF.ContinuousOscillatorMemoryRefinementRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Core.RecursiveScaleTransitionExact as Scale
import DASHI.Cognition.PNF.ContinuousOscillatorMemoryRefinementExact as Osc
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PhaseEnrichedTrit as Phase

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

unitOscillatorSchema : Osc.OscillatorSchema
unitOscillatorSchema = record
  { Mode = ⊤
  ; Amplitude = ⊤
  ; Frequency = ⊤
  ; ContinuousPhase = ⊤
  ; Coupling = ⊤
  ; HiddenField = ⊤
  ; assembleMode = λ _ _ _ _ _ → tt
  }

unitHiddenOscillatorState : Osc.HiddenOscillatorState unitOscillatorSchema
unitHiddenOscillatorState = Osc.hiddenOscillatorState tt

------------------------------------------------------------------------
-- Boundary projections: the owner exposes these separations as typed claims
-- that later realisations must pay, rather than postulating them as identities.
------------------------------------------------------------------------

continuousPhaseBoundary : Osc.ContinuousOscillatorBoundary → Set
continuousPhaseBoundary boundary =
  Osc.continuousPhaseIsNotPhase3ByDefinition boundary

cognitiveDissonanceBoundary : Osc.ContinuousOscillatorBoundary → Set
cognitiveDissonanceBoundary boundary =
  Osc.mismatchIsNotCognitiveDissonanceByDefinition boundary

hebbianBoundary : Osc.ContinuousOscillatorBoundary → Set
hebbianBoundary boundary =
  Osc.gradientDescentIsNotHebbianByDefinition boundary

truthBoundary : Osc.ContinuousOscillatorBoundary → Set
truthBoundary boundary =
  Osc.coherenceIsNotTruthByDefinition boundary

stabilityBoundary : Osc.ContinuousOscillatorBoundary → Set
stabilityBoundary boundary =
  Osc.stableClassIsNotMinimumByDefinition boundary

temporalBoundary : Osc.ContinuousOscillatorBoundary → Set
temporalBoundary boundary =
  Osc.targetStateIsNotBackwardsCausation boundary

energyBoundary : Osc.ContinuousOscillatorBoundary → Set
energyBoundary boundary =
  Osc.objectiveDoesNotMergeAllEnergyCarriers boundary

------------------------------------------------------------------------
-- Memory identity remains semantic/event-level while hidden oscillator state
-- may vary.  Finite phase is reached only through an explicit observation map.
------------------------------------------------------------------------

hiddenChangeCanPreserveRememberedEvent :
  {Hidden : Set} →
  (refinement : Osc.OscillatorMemoryRefinement Hidden) →
  (x y : Hidden) →
  Osc.MemoryEquivalentHiddenState refinement x y →
  Memory.rememberedEvent (Osc.observeMemory refinement x) ≡
  Memory.rememberedEvent (Osc.observeMemory refinement y)
hiddenChangeCanPreserveRememberedEvent refinement x y equivalent =
  Osc.preservedRememberedEvent refinement x y equivalent

finitePhaseObservationIsExplicit :
  {Hidden : Set} →
  Osc.OscillatorMemoryRefinement Hidden →
  Hidden →
  Phase.PhaseEnrichedTrit
finitePhaseObservationIsExplicit refinement =
  Osc.observeFinitePhase refinement
