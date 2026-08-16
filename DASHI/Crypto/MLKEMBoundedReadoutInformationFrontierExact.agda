module DASHI.Crypto.MLKEMBoundedReadoutInformationFrontierExact where

------------------------------------------------------------------------
-- ML-KEM: BOUNDED READOUT INFORMATION FRONTIER
--
-- PURPOSE
--
-- MLKEMTouchInformationNoGoExact shows that touch count alone does not bound
-- protected-label information: one touched cell may have a large alphabet.
-- This module records the missing finite-capacity premise explicitly.
--
-- For a concrete representation/readout architecture let
--
--   t = touched state cells,
--   b = admitted information capacity per touched cell (bits),
--   g = observation information exposed by the readout (bits),
--   p = protected-label information resolved by that observation (bits).
--
-- If
--
--   g <= t*b
--   p <= g,
--
-- then
--
--   p <= t*b.
--
-- This is deliberately a capacity/accounting theorem rather than an entropy
-- theorem.  A real cryptographic instantiation must justify both inequalities
-- for its exact state representation and observation/readout protocol.
--
-- Combining this information frontier with the existing uncertainty/touch
-- frontier gives two simultaneous obligations on the same primitive:
--
--   128 <= s*(t + sigma)
--   p   <= t*b.
--
-- That pair is the correct next surface for compressed sufficient states.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_; _*_ ; _+_)
import Data.Nat.Properties as NatP

record BoundedTouchReadout : Set where
  constructor bounded-touch-readout
  field
    touchCount : Nat
    bitsPerTouchedCell : Nat
    observationBits : Nat
    protectedBitsResolved : Nat

    observationWithinTouchedCapacity :
      observationBits ≤ touchCount * bitsPerTouchedCell

    protectedResolutionWithinObservation :
      protectedBitsResolved ≤ observationBits

open BoundedTouchReadout public

protectedResolutionWithinTouchedCapacity :
  (readout : BoundedTouchReadout) →
  protectedBitsResolved readout ≤
  touchCount readout * bitsPerTouchedCell readout
protectedResolutionWithinTouchedCapacity readout =
  NatP.≤-trans
    (protectedResolutionWithinObservation readout)
    (observationWithinTouchedCapacity readout)

------------------------------------------------------------------------
-- Same-object joint uncertainty + readout frontier.
------------------------------------------------------------------------

record UncertaintyBoundedReadoutPrimitive : Set where
  constructor uncertainty-bounded-readout-primitive
  field
    sourceSupport : Nat
    singularBudget : Nat
    readout : BoundedTouchReadout

    uncertaintyTouch128 :
      128 ≤ sourceSupport * (touchCount readout + singularBudget)

open UncertaintyBoundedReadoutPrimitive public

primitiveUncertaintyFrontier :
  (primitive : UncertaintyBoundedReadoutPrimitive) →
  128 ≤
  sourceSupport primitive *
  (touchCount (readout primitive) + singularBudget primitive)
primitiveUncertaintyFrontier = uncertaintyTouch128

primitiveInformationFrontier :
  (primitive : UncertaintyBoundedReadoutPrimitive) →
  protectedBitsResolved (readout primitive) ≤
  touchCount (readout primitive) * bitsPerTouchedCell (readout primitive)
primitiveInformationFrontier primitive =
  protectedResolutionWithinTouchedCapacity (readout primitive)

------------------------------------------------------------------------
-- Radius specialization.  If primitive source moves are bounded by r, the
-- same-object uncertainty frontier survives with r in place of actual support.
------------------------------------------------------------------------

radiusUncertaintyFrontier :
  (primitive : UncertaintyBoundedReadoutPrimitive) →
  (radius : Nat) →
  sourceSupport primitive ≤ radius →
  128 ≤
  radius *
  (touchCount (readout primitive) + singularBudget primitive)
radiusUncertaintyFrontier primitive radius withinRadius =
  NatP.≤-trans
    (uncertaintyTouch128 primitive)
    (NatP.*-monoˡ-≤
      (touchCount (readout primitive) + singularBudget primitive)
      withinRadius)

------------------------------------------------------------------------
-- AUTHORITY BOUNDARY
--
-- The theorem does NOT assert that one ML-KEM residual cell carries a specific
-- number of useful attacker bits.  For an F_q or F_{q^2} materialized cell the
-- raw alphabet may be large, while a protocol-visible predicate may expose far
-- less.  The producer that matters is therefore readout-specific:
--
--   protected-resolution <= admitted readout information
--   admitted readout information <= touched-state capacity.
--
-- Without those same-object facts, neither touch count nor harmonic support is
-- an information-theoretic hardness theorem.
------------------------------------------------------------------------
