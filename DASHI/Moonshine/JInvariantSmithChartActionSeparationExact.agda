module DASHI.Moonshine.JInvariantSmithChartActionSeparationExact where

------------------------------------------------------------------------
-- SMITH HALF-TURN vs MODULAR REFLECTION / MODULAR T
--
-- On the common finite HexTruth presentation:
--
--   Smith admittance observer action:
--       h |-> h + 3 mod 6
--
--   modular reflection observer action:
--       h |-> -h mod 6
--
--   modular T on the phase lane:
--       h |-> h
--
-- These are different actions at C6.
--
-- However the existing C6 -> C3 orientation-forgetting quotient cannot see
-- the Smith half-turn: +3 mod 6 preserves the triadic phase quotient.
--
-- This is a concrete example of why equality after a coarse phase observer
-- does not imply equality of the underlying symmetry/action.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Base369 as Base
import DASHI.Foundations.Base369MobiusTransport as HalfTurn
import DASHI.Moonshine.JInvariant369ReflectionEquivarianceExact as Reflection

hex0NotHex3 : Base.hex-0 ≡ Base.hex-3 → ⊥
hex0NotHex3 ()

HalfTurnIsPhaseIdentity : Set
HalfTurnIsPhaseIdentity =
  (x : Base.HexTruth) →
  HalfTurn.mobiusTransport x ≡ x

smithHalfTurnIsNotModularTPhaseIdentity :
  ¬ HalfTurnIsPhaseIdentity
smithHalfTurnIsNotModularTPhaseIdentity same =
  hex0NotHex3 (same Base.hex-0)

HalfTurnIsModularReflection : Set
HalfTurnIsModularReflection =
  (x : Base.HexTruth) →
  HalfTurn.mobiusTransport x
  ≡ Reflection.reflect6 x

smithHalfTurnIsNotModularReflection :
  ¬ HalfTurnIsModularReflection
smithHalfTurnIsNotModularReflection same =
  hex0NotHex3 (same Base.hex-0)

------------------------------------------------------------------------
-- Yet the orientation-forgetting C3 quotient erases the Smith half-turn.
------------------------------------------------------------------------

c3QuotientCannotSeeSmithHalfTurn :
  (x : Base.HexTruth) →
  HalfTurn.hexTriadicPhase
    (HalfTurn.mobiusTransport x)
  ≡
  HalfTurn.hexTriadicPhase x
c3QuotientCannotSeeSmithHalfTurn =
  HalfTurn.mobiusTransport-preservesTriadicPhase

------------------------------------------------------------------------
-- Coarse-observer action collision.
------------------------------------------------------------------------

record ActionCollisionUnderObserver
    (State Observation : Set)
    (observe : State → Observation) : Set₁ where
  field
    leftAction rightAction : State → State
    sameObservedAction :
      (x : State) →
      observe (leftAction x) ≡ observe (rightAction x)
    witness : State
    actionsDifferAtWitness :
      leftAction witness ≡ rightAction witness → ⊥

open ActionCollisionUnderObserver public

identityHex : Base.HexTruth → Base.HexTruth
identityHex x = x

identityVsSmithHalfTurnCollideAtC3 :
  ActionCollisionUnderObserver
    Base.HexTruth
    Base.TriTruth
    HalfTurn.hexTriadicPhase
identityVsSmithHalfTurnCollideAtC3 = record
  { leftAction = identityHex
  ; rightAction = HalfTurn.mobiusTransport
  ; sameObservedAction =
      λ x →
        sym
          (HalfTurn.mobiusTransport-preservesTriadicPhase x)
  ; witness = Base.hex-0
  ; actionsDifferAtWitness =
      λ same →
        hex0NotHex3 (sym same)
  }

C3ObserverDeterminesHexAction : Set
C3ObserverDeterminesHexAction =
  (f g : Base.HexTruth → Base.HexTruth) →
  ((x : Base.HexTruth) →
    HalfTurn.hexTriadicPhase (f x)
    ≡ HalfTurn.hexTriadicPhase (g x)) →
  (x : Base.HexTruth) →
  f x ≡ g x

c3ObserverDoesNotDetermineUnderlyingHexAction :
  ¬ C3ObserverDeterminesHexAction
c3ObserverDoesNotDetermineUnderlyingHexAction exact =
  actionsDifferAtWitness identityVsSmithHalfTurnCollideAtC3
    (exact
      identityHex
      HalfTurn.mobiusTransport
      (sameObservedAction
        identityVsSmithHalfTurnCollideAtC3)
      Base.hex-0)

record SmithModularActionSeparationBoundary : Set where
  constructor smith-modular-action-separation-boundary
  field
    smithHalfTurnDistinctFromModularTOnC6 : Bool
    smithHalfTurnDistinctFromModularReflectionOnC6 : Bool
    c3QuotientErasesSmithHalfTurn : Bool
    explicitIdentityHalfTurnActionCollisionAtC3Owned : Bool
    c3ObserverDoesNotDetermineUnderlyingC6Action : Bool

    equalityAtC3ImpliesSameC6Action : Bool
    sameSixStateCardinalityImpliesSameAction : Bool
    smithAdmittanceIsModularSymmetry : Bool

canonicalSmithModularActionSeparationBoundary :
  SmithModularActionSeparationBoundary
canonicalSmithModularActionSeparationBoundary =
  smith-modular-action-separation-boundary
    true true true true true
    false false false
