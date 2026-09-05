{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Lithography.DepthOfFocusScalingExact where

open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.Semiconductor.Lithography.ASMLRayleighFixturesExact

-- Finite carrier for the standard idealized lithographic depth-of-focus
-- scaling
--
--   DOF = k₂ λ / NA²
--
-- represented without division as
--
--   DOF · NA² = k₂ · λ.
--
-- As with the Rayleigh CD carrier, this is a model seam rather than a claim
-- that a complete physical process window is determined by this equation.

record DepthOfFocusCoordinates : Set where
  constructor depthOfFocusCoordinates
  field
    dof        : Nat
    k2         : Nat
    wavelength : Nat
    na         : Nat

open DepthOfFocusCoordinates public

DepthOfFocusLaw : DepthOfFocusCoordinates → Set
DepthOfFocusLaw x =
  dof x * (na x * na x) ≡ k2 x * wavelength x

-- Holding λ and k₂ fixed, NA 0.33 -> 0.55 gives the exact normalized
-- inverse-square relation
--
--   25 · 33² = 9 · 55².
--
-- Thus the idealized DOF coordinate scales by 9/25 between these aperture
-- coordinates.  This is deliberately not promoted to an on-product process-
-- window theorem: resist, mask, illumination, aberration and control terms
-- remain outside this finite fixture.
highNaInverseSquareApertureScaling :
  25 * (standardEuvNAHundredths * standardEuvNAHundredths) ≡
  9 * (highEuvNAHundredths * highEuvNAHundredths)
highNaInverseSquareApertureScaling = refl

-- Normalized executable witnesses for the same relation.  27225 is chosen as
-- a common finite numerator solely to make the scaling exact by reduction.
standardNaNormalizedDepthOfFocus : DepthOfFocusCoordinates
standardNaNormalizedDepthOfFocus =
  depthOfFocusCoordinates 25 1 27225 standardEuvNAHundredths

standardNaNormalizedDepthOfFocusLaw :
  DepthOfFocusLaw standardNaNormalizedDepthOfFocus
standardNaNormalizedDepthOfFocusLaw = refl

highNaNormalizedDepthOfFocus : DepthOfFocusCoordinates
highNaNormalizedDepthOfFocus =
  depthOfFocusCoordinates 9 1 27225 highEuvNAHundredths

highNaNormalizedDepthOfFocusLaw :
  DepthOfFocusLaw highNaNormalizedDepthOfFocus
highNaNormalizedDepthOfFocusLaw = refl
