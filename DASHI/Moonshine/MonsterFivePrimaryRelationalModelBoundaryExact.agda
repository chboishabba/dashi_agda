module DASHI.Moonshine.MonsterFivePrimaryRelationalModelBoundaryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- John H. Conway and Simon P. Norton,
-- "Monstrous Moonshine",
-- Bulletin of the London Mathematical Society 11 (1979), 308--339.
-- DOI: 10.1112/blms/11.3.308.
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents",
-- arXiv:2602.09135.  No DOI asserted for the preprint.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups",
-- Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- The exact finite five-mode/two-phase quotient is already constructed.  This
-- file states the smallest actual Monster-5-local promotion contract: an
-- observer on a genuine carrier must intertwine actual transport with transport
-- on the nine-state model.  No equivalence between the entire actual carrier
-- and nine states is demanded or fabricated.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.Base369FiveModePhaseQuotientExact as Model

record MonsterFivePrimaryRelationalObserver : Set₁ where
  constructor mkMonsterFivePrimaryRelationalObserver
  field
    ActualState : Set
    ActualTransport : Set

    applyActualTransport : ActualTransport → ActualState → ActualState
    observeStableMode : ActualState → Model.ModePhaseQuotient9
    modelTransport : ActualTransport →
      Model.ModePhaseQuotient9 → Model.ModePhaseQuotient9

    observerIntertwines :
      (transport : ActualTransport) →
      (state : ActualState) →
      observeStableMode (applyActualTransport transport state)
      ≡ modelTransport transport (observeStableMode state)

    completionWitness : ActualState → Bool

open MonsterFivePrimaryRelationalObserver public

record MonsterFivePrimaryPromotionBoundary : Set where
  constructor mkMonsterFivePrimaryPromotionBoundary
  field
    actualFiveLocalCarrierIdentified : Bool
    actualFiveLocalCarrierIdentifiedIsFalse :
      actualFiveLocalCarrierIdentified ≡ false
    actualNineChannelObserverConstructed : Bool
    actualNineChannelObserverConstructedIsFalse :
      actualNineChannelObserverConstructed ≡ false
    actualTransportIntertwinerProved : Bool
    actualTransportIntertwinerProvedIsFalse :
      actualTransportIntertwinerProved ≡ false

canonicalMonsterFivePrimaryPromotionBoundary :
  MonsterFivePrimaryPromotionBoundary
canonicalMonsterFivePrimaryPromotionBoundary =
  mkMonsterFivePrimaryPromotionBoundary
    false refl
    false refl
    false refl
