module DASHI.Physics.QuantumVacuum.HarmonicOscillatorRationalHalfScaleExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

import DASHI.Physics.QuantumVacuum.HarmonicOscillatorDoubledEnergyExact as Doubled

------------------------------------------------------------------------
-- CONCRETE RATIONAL HALF-SCALE BRIDGE
--
-- The denominator-free owner carries
--
--   2 E_n = (2 n + 1) hbar omega.
--
-- This module proves in the repository's normalized rational carrier that
-- division by two gives exactly the usual oscillator expression
--
--   E_n = hbar omega (n + 1/2).
--
-- The proof is pure rational-ring algebra and does not import any QFT or
-- extraction semantics.
------------------------------------------------------------------------

half : ℚ
half = + 1 / 2

two : ℚ
two = 1ℚ + 1ℚ

rationalHalfScaleIdentity :
  (hbar omega n : ℚ) →
  (((two * n + 1ℚ) * (hbar * omega)) * half)
  ≡ (hbar * omega) * (n + half)
rationalHalfScaleIdentity hbar omega n =
  ℚRing.solve (hbar ∷ omega ∷ n ∷ [])

rationalGroundHalfScaleIdentity :
  (hbar omega : ℚ) →
  ((hbar * omega) * half)
  ≡ (hbar * omega) * (0ℚ + half)
rationalGroundHalfScaleIdentity hbar omega =
  ℚRing.solve (hbar ∷ omega ∷ [])

------------------------------------------------------------------------
-- Interpretation receipt for the denominator-free finite owner.
------------------------------------------------------------------------

record RationalHalfScaleReceipt : Set where
  field
    hbar omega occupation : ℚ
    doubledCoordinate : ℚ

    doubledCoordinateLaw :
      doubledCoordinate ≡
      (two * occupation + 1ℚ) * (hbar * omega)

    physicalEnergy : ℚ

    physicalEnergyLaw :
      physicalEnergy ≡ doubledCoordinate * half

    oscillatorLaw :
      physicalEnergy ≡
      (hbar * omega) * (occupation + half)

open RationalHalfScaleReceipt public

buildRationalHalfScaleReceipt :
  (hbar omega occupation : ℚ) →
  RationalHalfScaleReceipt
buildRationalHalfScaleReceipt hbar omega occupation =
  record
    { hbar = hbar
    ; omega = omega
    ; occupation = occupation
    ; doubledCoordinate =
        (two * occupation + 1ℚ) * (hbar * omega)
    ; doubledCoordinateLaw = refl
    ; physicalEnergy =
        ((two * occupation + 1ℚ) * (hbar * omega)) * half
    ; physicalEnergyLaw = refl
    ; oscillatorLaw = rationalHalfScaleIdentity hbar omega occupation
    }

------------------------------------------------------------------------
-- Authority firewall.
------------------------------------------------------------------------

rationalIdentityIsQFTRenormalisation : Bool
rationalIdentityIsQFTRenormalisation = false

rationalIdentityIsExtractionReceipt : Bool
rationalIdentityIsExtractionReceipt = false

rationalIdentityIsQFTRenormalisationIsFalse :
  rationalIdentityIsQFTRenormalisation ≡ false
rationalIdentityIsQFTRenormalisationIsFalse = refl

rationalIdentityIsExtractionReceiptIsFalse :
  rationalIdentityIsExtractionReceipt ≡ false
rationalIdentityIsExtractionReceiptIsFalse = refl
