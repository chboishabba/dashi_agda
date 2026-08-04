module DASHI.Physics.Closure.NSTriadKNLuoIncrementKernelMultiplierIdentityExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- Communications in Mathematical Physics 165 (1994), 207--209.
-- DOI: 10.1007/BF02099744.
--
-- PURPOSE
-- Prove the exact coefficient algebra behind Luo's increment-kernel identity.
-- If chiK, chiL and chiOutput are the low-pass symbols at k, l and k+l, then
--
--   rMultiplier = chiOutput - chiK - chiL + 1,
--   highHigh    = (1-chiK)(1-chiL),
--   lowLow      = chiK chiL,
--
-- and rMultiplier - highHigh + lowLow = chiOutput.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational using (ℚ; 1ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing

incrementMultiplier : ℚ → ℚ → ℚ → ℚ
incrementMultiplier chiK chiL chiOutput =
  chiOutput - chiK - chiL + 1ℚ

highHighMultiplier : ℚ → ℚ → ℚ
highHighMultiplier chiK chiL =
  (1ℚ - chiK) * (1ℚ - chiL)

lowLowMultiplier : ℚ → ℚ → ℚ
lowLowMultiplier chiK chiL = chiK * chiL

luoIncrementMultiplierIdentity :
  (chiK chiL chiOutput : ℚ) →
  incrementMultiplier chiK chiL chiOutput
    - highHighMultiplier chiK chiL
    + lowLowMultiplier chiK chiL
  ≡ chiOutput
luoIncrementMultiplierIdentity chiK chiL chiOutput =
  ℚRing.solve (chiK ∷ chiL ∷ chiOutput ∷ [])

record ResonantMultiplierData : Set where
  field
    chiLeft chiRight chiOutput : ℚ

open ResonantMultiplierData public

projectedProductMultiplier : ResonantMultiplierData → ℚ
projectedProductMultiplier data = chiOutput data

incrementKernelCoefficient : ResonantMultiplierData → ℚ
incrementKernelCoefficient data =
  incrementMultiplier
    (chiLeft data) (chiRight data) (chiOutput data)

highHighCoefficient : ResonantMultiplierData → ℚ
highHighCoefficient data =
  highHighMultiplier (chiLeft data) (chiRight data)

lowLowCoefficient : ResonantMultiplierData → ℚ
lowLowCoefficient data =
  lowLowMultiplier (chiLeft data) (chiRight data)

coefficientwiseProjectedTensorIdentity :
  (data : ResonantMultiplierData) →
  incrementKernelCoefficient data
    - highHighCoefficient data
    + lowLowCoefficient data
  ≡ projectedProductMultiplier data
coefficientwiseProjectedTensorIdentity data =
  luoIncrementMultiplierIdentity
    (chiLeft data) (chiRight data) (chiOutput data)

record SpatialIncrementFourierCoefficientIdentification : Set₁ where
  field
    triadCoefficient : ℚ
    multiplierData : ResonantMultiplierData

    spatialIncrementCoefficient : ℚ
    spatialIncrementCoefficientMeaning :
      spatialIncrementCoefficient
      ≡ incrementKernelCoefficient multiplierData * triadCoefficient

    projectedProductCoefficient : ℚ
    projectedProductCoefficientMeaning :
      projectedProductCoefficient
      ≡ projectedProductMultiplier multiplierData * triadCoefficient

    highHighProductCoefficient : ℚ
    highHighProductCoefficientMeaning :
      highHighProductCoefficient
      ≡ highHighCoefficient multiplierData * triadCoefficient

    lowLowProductCoefficient : ℚ
    lowLowProductCoefficientMeaning :
      lowLowProductCoefficient
      ≡ lowLowCoefficient multiplierData * triadCoefficient

open SpatialIncrementFourierCoefficientIdentification public

spatialIncrementGivesProjectedProductCoefficient :
  (identification : SpatialIncrementFourierCoefficientIdentification) →
  spatialIncrementCoefficient identification
    - highHighProductCoefficient identification
    + lowLowProductCoefficient identification
  ≡ projectedProductCoefficient identification
spatialIncrementGivesProjectedProductCoefficient identification
  rewrite spatialIncrementCoefficientMeaning identification
        | highHighProductCoefficientMeaning identification
        | lowLowProductCoefficientMeaning identification
        | projectedProductCoefficientMeaning identification =
  ℚRing.solve
    (chiLeft (multiplierData identification)
      ∷ chiRight (multiplierData identification)
      ∷ chiOutput (multiplierData identification)
      ∷ triadCoefficient identification
      ∷ [])

incrementMultiplierAlgebraClosed : Bool
incrementMultiplierAlgebraClosed = true

projectedTensorCoefficientIdentityClosed : Bool
projectedTensorCoefficientIdentityClosed = true

incrementMultiplierAlgebraClosedIsTrue :
  incrementMultiplierAlgebraClosed ≡ true
incrementMultiplierAlgebraClosedIsTrue = refl

projectedTensorCoefficientIdentityClosedIsTrue :
  projectedTensorCoefficientIdentityClosed ≡ true
projectedTensorCoefficientIdentityClosedIsTrue = refl
