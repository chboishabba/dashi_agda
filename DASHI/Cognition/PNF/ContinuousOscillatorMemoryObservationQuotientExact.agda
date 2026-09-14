module DASHI.Cognition.PNF.ContinuousOscillatorMemoryObservationQuotientExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl; cong)

import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PNF.ContinuousOscillatorMemoryRefinementExact as Parent
import DASHI.Cognition.PNF.ContinuousOscillatorIdentifiabilityReceipt as Ident

------------------------------------------------------------------------
-- EXPLICIT CONTINUOUS-STATE -> MEMORY OBSERVATION QUOTIENT
--
-- The structural parent already supplies `observeMemory`.  This owner makes
-- the quotient obligation explicit rather than treating a lower-scale stable
-- class as identical to a semantic memory object.  A declared hidden
-- equivalence must be sound for the whole public MemoryFibre observation.
------------------------------------------------------------------------

record MemoryObservationQuotient (Hidden : Set) : Set₁ where
  constructor memory-observation-quotient
  field
    refinement : Parent.OscillatorMemoryRefinement Hidden
    EquivalentHidden : Hidden → Hidden → Set
    equivalentReflexive : (x : Hidden) → EquivalentHidden x x
    observeMemorySound :
      (x y : Hidden) →
      EquivalentHidden x y →
      Parent.observeMemory refinement x ≡ Parent.observeMemory refinement y
open MemoryObservationQuotient public

rememberedEventSound :
  ∀ {Hidden} →
  (quotient : MemoryObservationQuotient Hidden) →
  (x y : Hidden) →
  EquivalentHidden quotient x y →
  Memory.rememberedEvent
    (Parent.observeMemory (refinement quotient) x)
  ≡
  Memory.rememberedEvent
    (Parent.observeMemory (refinement quotient) y)
rememberedEventSound quotient x y equivalent =
  cong Memory.rememberedEvent
    (observeMemorySound quotient x y equivalent)

------------------------------------------------------------------------
-- A public-memory collision is only a hidden-recovery obstruction when the
-- hidden query actually separates the colliding states.  This is exactly the
-- query-relative lesson from the identifiability parent.
------------------------------------------------------------------------

record HiddenRecoveryCollision
    (Hidden Answer : Set)
    (quotient : MemoryObservationQuotient Hidden)
    (hiddenQuery : Hidden → Answer) : Set₁ where
  constructor hidden-recovery-collision
  field
    left right : Hidden
    samePublicMemory :
      Parent.observeMemory (refinement quotient) left
      ≡ Parent.observeMemory (refinement quotient) right
    hiddenAnswerDistinct : hiddenQuery left ≡ hiddenQuery right → ⊥
open HiddenRecoveryCollision public

hiddenStateIdentifiabilityQueryRetained : Ident.OscillatorIdentifiabilityQuery
hiddenStateIdentifiabilityQueryRetained = Ident.hiddenStateQuery

------------------------------------------------------------------------
-- The quotient is an observation/semantic interface, not a declaration that
-- every hidden coordinate is irrelevant, nor an empirical brain mechanism.
------------------------------------------------------------------------

record ContinuousOscillatorMemoryQuotientBoundary : Set where
  constructor continuous-oscillator-memory-quotient-boundary
  field
    sameRememberedEventImpliesSameWholeMemoryFibre : Bool
    sameWholeMemoryFibreImpliesSameHiddenState : Bool
    quotientErasesAllHiddenCoordinatesByDefinition : Bool
    hiddenCollisionCreatesNeuroscienceMechanism : Bool
    memoryObservationCreatesPhysicalScaleRealisation : Bool
    stableClassAutomaticallyRealisesMemory : Bool
    queryRelativeIdentifiabilityRetained : Bool
    explicitObservationWitnessRequired : Bool
open ContinuousOscillatorMemoryQuotientBoundary public

canonicalContinuousOscillatorMemoryQuotientBoundary :
  ContinuousOscillatorMemoryQuotientBoundary
canonicalContinuousOscillatorMemoryQuotientBoundary =
  continuous-oscillator-memory-quotient-boundary
    false false false false false false true true
