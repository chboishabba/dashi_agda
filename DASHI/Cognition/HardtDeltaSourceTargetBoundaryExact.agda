module DASHI.Cognition.HardtDeltaSourceTargetBoundaryExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Owner: Hardt Delta steelman PR #1252, stacked on Psychotronics PR #1242
-- Exact FINITE observation counterexample; not a calibrated EEG/MEG model.
-- A scalp observation is not definitionally an emitting source or target
-- coupling. Physical measurement and source identification remain separate.
------------------------------------------------------------------------

record TwoSourceState : Set where
  constructor two-source
  field
    sourceA : Nat
    sourceB : Nat
open TwoSourceState public

eegSum : TwoSourceState → Nat
eegSum s = sourceA s + sourceB s

firstSourceProjection : TwoSourceState → Nat
firstSourceProjection s = sourceA s

stateOne : TwoSourceState
stateOne = two-source 1 0

stateTwo : TwoSourceState
stateTwo = two-source 0 1

sameEEG : eegSum stateOne ≡ eegSum stateTwo
sameEEG = refl

-- There is no universal function from equality of this EEG observation to
-- equality of a DISTINCT source projection without further premises.
noUniversalEEGToSourceProjection :
  ((x y : TwoSourceState) →
    eegSum x ≡ eegSum y →
    firstSourceProjection x ≡ firstSourceProjection y) → ⊥
noUniversalEEGToSourceProjection assumed with
  assumed stateOne stateTwo sameEEG
... | ()

------------------------------------------------------------------------
-- Exchangeable, UNADDRESSED receivers.
-- This model postulates identical source-to-receiver responses; it does
-- not assert that real receivers, distances, or tissue are identical.
-- A source-specific field geometry or an authenticated address would break
-- this assumption, which is exactly what a steelman must provide.
------------------------------------------------------------------------

data UnaddressedTwoReceiver : Set where
  anonymous-pair : (sharedResponse : Nat) → UnaddressedTwoReceiver

receiverA : UnaddressedTwoReceiver → Nat
receiverA (anonymous-pair r) = r

receiverB : UnaddressedTwoReceiver → Nat
receiverB (anonymous-pair r) = r

anonymousExchangeInvariance :
  (r : UnaddressedTwoReceiver) → receiverA r ≡ receiverB r
anonymousExchangeInvariance (anonymous-pair r) = refl

-- An exchangeable, unlabeled two-receiver source cannot, IN THIS MODEL,
-- output one on receiver A and zero on receiver B.
noUniqueFirstReceiver :
  (r : UnaddressedTwoReceiver) →
  receiverA r ≡ 1 → receiverB r ≡ 0 → ⊥
noUniqueFirstReceiver (anonymous-pair zero) () _
noUniqueFirstReceiver (anonymous-pair (suc n)) _ ()

------------------------------------------------------------------------
-- Untouched evidence boundaries: these are empty REQUIREMENT TYPES,
-- not purported proofs that extraordinary physics is impossible.
------------------------------------------------------------------------

data ActualEEGCurrentForwardCalibration : Set where
data AuthenticatedTargetAddressMechanism : Set where
data IndependentBlindedRemoteEffect : Set where

record PhysicalTargetPromotion : Set where
  field
    sourceReceipt : ActualEEGCurrentForwardCalibration
    targetReceipt : AuthenticatedTargetAddressMechanism
    causalReceipt : IndependentBlindedRemoteEffect
