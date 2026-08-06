module DASHI.Biology.MoonshineModularFormCoefficientExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John H. Conway and Simon P. Norton,
-- "Monstrous Moonshine".
-- DOI: 10.1112/blms/11.3.308.
--
-- Igor B. Frenkel, James Lepowsky and Arne Meurman,
-- "A Natural Representation of the Fischer-Griess Monster with the Modular
-- Function J as Character".
-- DOI: 10.1073/pnas.81.10.3256.
--
-- Richard E. Borcherds,
-- "Monstrous Moonshine and Monstrous Lie Superalgebras".
-- DOI: 10.1007/BF01232032.
--
-- DASHI CONTRIBUTION
--
-- Compute, rather than merely record, the first four coefficients of
--
--                 j(q) = E4(q)^3 / Delta(q)
--
-- from finite coefficient convolution.  With
--
--   E4^3 = 1 + 720 q + 179280 q^2 + 16954560 q^3 + ...
--   1/Delta = q^-1 + 24 + 324 q + 3200 q^2 + ...,
--
-- the convolution gives
--
--   j = q^-1 + 744 + 196884 q + 21493760 q^2 + ...,
--   J = j - 744
--     = q^-1 + 196884 q + 21493760 q^2 + ... .
--
-- The c=24 shifted Moonshine character prefix is then identified exactly with
-- this normalized-J prefix.  This finite coefficient theorem does not prove
-- modular transformation laws, genus zero, replicability or the existence of
-- the Moonshine VOA.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_+_; _*_)

------------------------------------------------------------------------
-- Finite coefficient data.
------------------------------------------------------------------------

e4CubedQ0 e4CubedQ1 e4CubedQ2 e4CubedQ3 : Nat
e4CubedQ0 = 1
e4CubedQ1 = 720
e4CubedQ2 = 179280
e4CubedQ3 = 16954560

deltaInverseQMinus1 deltaInverseQ0 deltaInverseQ1 deltaInverseQ2 : Nat
deltaInverseQMinus1 = 1
deltaInverseQ0 = 24
deltaInverseQ1 = 324
deltaInverseQ2 = 3200

jCoefficientMinus1 : Nat
jCoefficientMinus1 = e4CubedQ0 * deltaInverseQMinus1

jCoefficientZero : Nat
jCoefficientZero =
  e4CubedQ0 * deltaInverseQ0
  + e4CubedQ1 * deltaInverseQMinus1

jCoefficientOne : Nat
jCoefficientOne =
  e4CubedQ0 * deltaInverseQ1
  + e4CubedQ1 * deltaInverseQ0
  + e4CubedQ2 * deltaInverseQMinus1

jCoefficientTwo : Nat
jCoefficientTwo =
  e4CubedQ0 * deltaInverseQ2
  + e4CubedQ1 * deltaInverseQ1
  + e4CubedQ2 * deltaInverseQ0
  + e4CubedQ3 * deltaInverseQMinus1

jMinusOneExact : jCoefficientMinus1 ≡ 1
jMinusOneExact = refl

jConstantExact : jCoefficientZero ≡ 744
jConstantExact = refl

jCoefficientOneExact : jCoefficientOne ≡ 196884
jCoefficientOneExact = refl

jCoefficientTwoExact : jCoefficientTwo ≡ 21493760
jCoefficientTwoExact = refl

------------------------------------------------------------------------
-- Normalized J and the c/24 shift.
------------------------------------------------------------------------

data LaurentExponentPrefix : Set where
  exponentMinusOne : LaurentExponentPrefix
  exponentZero : LaurentExponentPrefix
  exponentOne : LaurentExponentPrefix
  exponentTwo : LaurentExponentPrefix

normalizedJCoefficient : LaurentExponentPrefix → Nat
normalizedJCoefficient exponentMinusOne = 1
normalizedJCoefficient exponentZero = 0
normalizedJCoefficient exponentOne = jCoefficientOne
normalizedJCoefficient exponentTwo = jCoefficientTwo

record MoonshineCharacterPrefix : Set where
  constructor moonshineCharacterPrefix
  field
    weightZeroDimension : Nat
    weightOneDimension : Nat
    weightTwoDimension : Nat
    weightThreeDimension : Nat

open MoonshineCharacterPrefix public

moonshineCharacter : MoonshineCharacterPrefix
moonshineCharacter = moonshineCharacterPrefix 1 0 196884 21493760

shiftedCharacterCoefficient :
  LaurentExponentPrefix → MoonshineCharacterPrefix → Nat
shiftedCharacterCoefficient exponentMinusOne profile =
  weightZeroDimension profile
shiftedCharacterCoefficient exponentZero profile =
  weightOneDimension profile
shiftedCharacterCoefficient exponentOne profile =
  weightTwoDimension profile
shiftedCharacterCoefficient exponentTwo profile =
  weightThreeDimension profile

moonshineCharacterMatchesNormalizedJPrefix :
  (exponent : LaurentExponentPrefix) →
  shiftedCharacterCoefficient exponent moonshineCharacter
  ≡ normalizedJCoefficient exponent
moonshineCharacterMatchesNormalizedJPrefix exponentMinusOne = refl
moonshineCharacterMatchesNormalizedJPrefix exponentZero = refl
moonshineCharacterMatchesNormalizedJPrefix exponentOne =
  jCoefficientOneExact
moonshineCharacterMatchesNormalizedJPrefix exponentTwo =
  jCoefficientTwoExact

record ModularFormAuthorityBoundary : Set where
  constructor modularFormAuthorityBoundary
  field
    finiteCoefficientConvolutionProvesSL2ZModularity : Set
    finiteCoefficientConvolutionDoesNotProveSL2ZModularity :
      finiteCoefficientConvolutionProvesSL2ZModularity → Set

    normalizedJPrefixConstructsMoonshineVOA : Set
    normalizedJPrefixDoesNotConstructMoonshineVOA :
      normalizedJPrefixConstructsMoonshineVOA → Set

canonicalModularFormAuthorityBoundary : ModularFormAuthorityBoundary
canonicalModularFormAuthorityBoundary =
  modularFormAuthorityBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
  where
  open import Data.Empty using (⊥)
