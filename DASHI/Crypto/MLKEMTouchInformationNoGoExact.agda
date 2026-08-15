module DASHI.Crypto.MLKEMTouchInformationNoGoExact where

------------------------------------------------------------------------
-- ML-KEM: TOUCH COUNT DOES NOT BY ITSELF BOUND INFORMATION GAIN
--
-- PURPOSE
--
-- The exact-residual theorem lower-bounds a concrete update resource: how many
-- materialised residual cells must be touched.  It is tempting to infer that a
-- small touch count also means a small protected-label refinement.  That is
-- false without a bound on the information capacity of each touched cell.
--
-- A single touched cell can have an arbitrarily rich alphabet.  This finite
-- regression uses a four-valued cell and four hidden/protected states: one cell
-- observation is already injective.  Therefore any theorem of the form
--
--     touchCount <= t  ->  at most 2^t protected classes
--
-- needs an explicit bounded-cell-alphabet / bounded-readout premise.
--
-- This is a logical boundary theorem, not a claim about a real ML-KEM
-- implementation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- One touched four-valued cell can distinguish four states.
------------------------------------------------------------------------

data Hidden4 : Set where
  h0 h1 h2 h3 : Hidden4

data Cell4 : Set where
  c0 c1 c2 c3 : Cell4

observeOneCell : Hidden4 → Cell4
observeOneCell h0 = c0
observeOneCell h1 = c1
observeOneCell h2 = c2
observeOneCell h3 = c3

protectedLabel : Hidden4 → Cell4
protectedLabel = observeOneCell

oneCellSeparates01 : observeOneCell h0 ≡ observeOneCell h1 → ⊥
oneCellSeparates01 ()

oneCellSeparates02 : observeOneCell h0 ≡ observeOneCell h2 → ⊥
oneCellSeparates02 ()

oneCellSeparates03 : observeOneCell h0 ≡ observeOneCell h3 → ⊥
oneCellSeparates03 ()

oneCellSeparates12 : observeOneCell h1 ≡ observeOneCell h2 → ⊥
oneCellSeparates12 ()

oneCellSeparates13 : observeOneCell h1 ≡ observeOneCell h3 → ⊥
oneCellSeparates13 ()

oneCellSeparates23 : observeOneCell h2 ≡ observeOneCell h3 → ⊥
oneCellSeparates23 ()

------------------------------------------------------------------------
-- Injective readout: equality of the one-cell observation forces equality of
-- hidden states.  Thus one touched cell can carry all four protected labels.
------------------------------------------------------------------------

oneCellObservationInjective :
  (x y : Hidden4) →
  observeOneCell x ≡ observeOneCell y →
  x ≡ y
oneCellObservationInjective h0 h0 refl = refl
oneCellObservationInjective h0 h1 ()
oneCellObservationInjective h0 h2 ()
oneCellObservationInjective h0 h3 ()
oneCellObservationInjective h1 h0 ()
oneCellObservationInjective h1 h1 refl = refl
oneCellObservationInjective h1 h2 ()
oneCellObservationInjective h1 h3 ()
oneCellObservationInjective h2 h0 ()
oneCellObservationInjective h2 h1 ()
oneCellObservationInjective h2 h2 refl = refl
oneCellObservationInjective h2 h3 ()
oneCellObservationInjective h3 h0 ()
oneCellObservationInjective h3 h1 ()
oneCellObservationInjective h3 h2 ()
oneCellObservationInjective h3 h3 refl = refl

------------------------------------------------------------------------
-- AUTHORITY BOUNDARY
--
-- What remains meaningful is a bounded-capacity statement:
--
--   number of touched cells
--   + capacity/alphabet of each touched cell
--   + readout protocol
--      -> maximum protected-label refinement.
--
-- Touch count alone cannot supply that theorem.
------------------------------------------------------------------------
