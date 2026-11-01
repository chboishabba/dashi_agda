module DASHI.Cognition.PNF.MultiTimescaleAccessLearningExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PNF.LearningAlgebra as Learning

------------------------------------------------------------------------
-- Three-timescale separation:
--
-- fast   : momentary phase/access control;
-- medium : network/excitability state;
-- slow   : learned/structural transition weight.
--
-- The finite model proves that each coordinate can change while the other two
-- remain fixed.  It does not assert universal biological timescale constants.
------------------------------------------------------------------------

record AccessLearningState : Set where
  constructor accessLearningState
  field
    fastPhase : Nat
    mediumExcitable : Bool
    slowWeight : Nat

open AccessLearningState public

baseline : AccessLearningState
baseline = accessLearningState zero false zero

fastStep : AccessLearningState → AccessLearningState
fastStep (accessLearningState phase excitable weight) =
  accessLearningState (suc phase) excitable weight

mediumStep : AccessLearningState → AccessLearningState
mediumStep (accessLearningState phase excitable weight) =
  accessLearningState phase true weight

slowStep : AccessLearningState → AccessLearningState
slowStep (accessLearningState phase excitable weight) =
  accessLearningState phase excitable (suc weight)

fastChangesOnlyFastCoordinate :
  fastStep baseline ≡ accessLearningState (suc zero) false zero
fastChangesOnlyFastCoordinate = refl

mediumChangesOnlyMediumCoordinate :
  mediumStep baseline ≡ accessLearningState zero true zero
mediumChangesOnlyMediumCoordinate = refl

slowChangesOnlySlowCoordinate :
  slowStep baseline ≡ accessLearningState zero false (suc zero)
slowChangesOnlySlowCoordinate = refl

fastNotMedium : fastStep baseline ≡ mediumStep baseline → ⊥
fastNotMedium ()

mediumNotSlow : mediumStep baseline ≡ slowStep baseline → ⊥
mediumNotSlow ()

fastNotSlow : fastStep baseline ≡ slowStep baseline → ⊥
fastNotSlow ()

------------------------------------------------------------------------
-- Existing memory learning supplies the slow/content-preserving analogue.
------------------------------------------------------------------------

phaseLearningPreservesEvent :
  (m : Memory.MemoryFibre) →
  (phase : Nat) →
  Memory.rememberedEvent
    (Learning.after (Learning.phaseRealignmentReceipt m phase))
  ≡ Memory.rememberedEvent m
phaseLearningPreservesEvent m phase = refl

reinforcementPreservesEvent :
  (m : Memory.MemoryFibre) →
  Memory.rememberedEvent
    (Learning.after (Learning.reinforcementReceipt m))
  ≡ Memory.rememberedEvent m
reinforcementPreservesEvent m = refl

record MultiTimescaleBoundary : Set where
  constructor multiTimescaleBoundary
  field
    fastChangeRequiresSlowRewrite : Bool
    mediumChangeIsSemanticRevision : Bool
    slowLearningErasesPriorSemanticEvent : Bool
    timescaleLabelsAreUniversalMeasuredConstants : Bool

canonicalMultiTimescaleBoundary : MultiTimescaleBoundary
canonicalMultiTimescaleBoundary =
  multiTimescaleBoundary false false false false
