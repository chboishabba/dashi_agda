{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.EUVOptics.BraggPhaseMatchingExact where

open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)

-- Exact finite carrier for the Bragg phase-matching relation
--
--   m λ = 2 d cos θ
--
-- with cos θ represented by an exact rational numerator/denominator pair.
-- The angle convention here is θ measured from the multilayer normal.
-- This is a phase-matching seam only: it does not by itself compute Fresnel
-- amplitudes, absorption, roughness, interdiffusion, stress or net reflectivity.

record BraggCoordinates : Set where
  constructor braggCoordinates
  field
    order          : Nat
    wavelength     : Nat
    period         : Nat
    cosNumerator   : Nat
    cosDenominator : Nat

open BraggCoordinates public

BraggLaw : BraggCoordinates → Set
BraggLaw x =
  order x * wavelength x * cosDenominator x ≡
  2 * period x * cosNumerator x

-- Normal-incidence first-order normalized fixture:
-- λ = 1350 and d = 675 in the same arbitrary length scale.
-- This encodes λ = 2 d exactly without claiming that 6.75 nm is the exact
-- production Mo/Si multilayer period of any current ASML/ZEISS mirror.
normalIncidenceFirstOrder : BraggCoordinates
normalIncidenceFirstOrder = braggCoordinates 1 1350 675 1 1

normalIncidenceFirstOrderLaw : BraggLaw normalIncidenceFirstOrder
normalIncidenceFirstOrderLaw = refl

-- If the period changes while wavelength/order/angle are fixed, phase matching
-- is not automatically preserved.  We store a deliberately mismatched fixture
-- as data for later non-equivalence tests rather than treating every multilayer
-- stack as interchangeable.
shiftedPeriod : BraggCoordinates
shiftedPeriod = braggCoordinates 1 1350 676 1 1
