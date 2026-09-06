module DASHI.Core.FiniteProbabilityDensityCoordinateWeldExact where

------------------------------------------------------------------------
-- FINITE PROBABILITY-DENSITY / COORDINATE-FUNCTION WELD
--
-- On a finite state carrier, a law density and a Euclidean coordinate vector
-- have the same underlying pointwise data:
--
--   State -> Scalar.
--
-- Probability normalization/nonnegativity are extra predicates on that carrier;
-- they do not create a different vector object.  This module makes the identity
-- rechart explicit so downstream TV consumers cannot accidentally introduce a
-- hidden carrier conversion.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Level; _⊔_; lsuc)

record FiniteDensityCoordinateCarrier (s ℓ : Level) : Set (lsuc (s ⊔ ℓ)) where
  field
    State : Set s
    Scalar : Set ℓ

open FiniteDensityCoordinateCarrier public

Density : ∀ {s ℓ} → FiniteDensityCoordinateCarrier s ℓ → Set (s ⊔ ℓ)
Density carrier = State carrier → Scalar carrier

CoordinateVector : ∀ {s ℓ} → FiniteDensityCoordinateCarrier s ℓ → Set (s ⊔ ℓ)
CoordinateVector carrier = State carrier → Scalar carrier

densityToCoordinates :
  ∀ {s ℓ} {carrier : FiniteDensityCoordinateCarrier s ℓ} →
  Density carrier → CoordinateVector carrier
densityToCoordinates density = density

coordinatesToDensity :
  ∀ {s ℓ} {carrier : FiniteDensityCoordinateCarrier s ℓ} →
  CoordinateVector carrier → Density carrier
coordinatesToDensity vector = vector

densityRoundTrip :
  ∀ {s ℓ} {carrier : FiniteDensityCoordinateCarrier s ℓ}
    (density : Density carrier) →
  coordinatesToDensity (densityToCoordinates density) ≡ density
densityRoundTrip density = refl

coordinateRoundTrip :
  ∀ {s ℓ} {carrier : FiniteDensityCoordinateCarrier s ℓ}
    (vector : CoordinateVector carrier) →
  densityToCoordinates (coordinatesToDensity vector) ≡ vector
coordinateRoundTrip vector = refl

record DensityCoordinateBoundary : Set where
  constructor densityCoordinateBoundary
  field
    samePointwiseCarrier : Bool
    probabilityNormalizationIsExtraPredicate : Bool
    nonnegativityIsExtraPredicate : Bool
    hiddenCarrierIsomorphismNeeded : Bool

canonicalDensityCoordinateBoundary : DensityCoordinateBoundary
canonicalDensityCoordinateBoundary =
  densityCoordinateBoundary true true true false

noHiddenCarrierConversion :
  DensityCoordinateBoundary.hiddenCarrierIsomorphismNeeded
    canonicalDensityCoordinateBoundary
  ≡ false
noHiddenCarrierConversion = refl
