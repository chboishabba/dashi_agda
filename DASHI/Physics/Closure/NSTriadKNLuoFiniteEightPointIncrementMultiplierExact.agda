module DASHI.Physics.Closure.NSTriadKNLuoFiniteEightPointIncrementMultiplierExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
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
-- Instantiate the literal weighted-increment multiplier identity on the
-- normalized eight-point torus:
--
--   integral phi (chi_k-1)(chi_l-1)
--     = hatPhi(k+l)-hatPhi(k)-hatPhi(l)+hatPhi(0).
--
-- Symmetry and both zero-mode cancellations are then derived.  Since every
-- mode of (Z/2Z)^3 is its own negative and all characters are real, the finite
-- conjugation law is exact but degenerate; the continuum Z^3 conjugate-pair
-- theorem still requires the genuine complex torus carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteEightPointTorusHaarExact as Torus

xorCommutative :
  (left right : Bool) →
  Torus.xor left right ≡ Torus.xor right left
xorCommutative false false = refl
xorCommutative false true = refl
xorCommutative true false = refl
xorCommutative true true = refl

addPointCommutative :
  (left right : Torus.BitTorus3) →
  Torus.addPoint left right ≡ Torus.addPoint right left
addPointCommutative
  (Torus.bit3 lx ly lz)
  (Torus.bit3 rx ry rz)
  rewrite xorCommutative lx rx
        | xorCommutative ly ry
        | xorCommutative lz rz = refl

addZeroLeft :
  (mode : Torus.BitTorus3) →
  Torus.addPoint Torus.zeroMode mode ≡ mode
addZeroLeft (Torus.bit3 mx my mz) = refl

addZeroRight :
  (mode : Torus.BitTorus3) →
  Torus.addPoint mode Torus.zeroMode ≡ mode
addZeroRight (Torus.bit3 false false false) = refl
addZeroRight (Torus.bit3 false false true) = refl
addZeroRight (Torus.bit3 false true false) = refl
addZeroRight (Torus.bit3 false true true) = refl
addZeroRight (Torus.bit3 true false false) = refl
addZeroRight (Torus.bit3 true false true) = refl
addZeroRight (Torus.bit3 true true false) = refl
addZeroRight (Torus.bit3 true true true) = refl

kernelTransform :
  (Torus.BitTorus3 → ℚ) → Torus.BitTorus3 → ℚ
kernelTransform kernel mode =
  Torus.haarAverage
    (λ point → kernel point * Torus.character mode point)

weightedIncrement :
  (Torus.BitTorus3 → ℚ) →
  Torus.BitTorus3 → Torus.BitTorus3 → ℚ
weightedIncrement kernel left right =
  Torus.haarAverage
    (λ point →
      kernel point
      * (Torus.character left point - 1ℚ)
      * (Torus.character right point - 1ℚ))

pairMultiplier :
  (Torus.BitTorus3 → ℚ) →
  Torus.BitTorus3 → Torus.BitTorus3 → ℚ
pairMultiplier kernel left right =
  kernelTransform kernel (Torus.addPoint left right)
  - kernelTransform kernel left
  - kernelTransform kernel right
  + kernelTransform kernel Torus.zeroMode

weightedIncrementMultiplierIdentity :
  (kernel : Torus.BitTorus3 → ℚ) →
  (left right : Torus.BitTorus3) →
  weightedIncrement kernel left right
  ≡ pairMultiplier kernel left right
weightedIncrementMultiplierIdentity kernel left right
  rewrite Torus.characterAdd left right Torus.p000
        | Torus.characterAdd left right Torus.p001
        | Torus.characterAdd left right Torus.p010
        | Torus.characterAdd left right Torus.p011
        | Torus.characterAdd left right Torus.p100
        | Torus.characterAdd left right Torus.p101
        | Torus.characterAdd left right Torus.p110
        | Torus.characterAdd left right Torus.p111 =
  solve
    ( kernel Torus.p000
    ∷ kernel Torus.p001
    ∷ kernel Torus.p010
    ∷ kernel Torus.p011
    ∷ kernel Torus.p100
    ∷ kernel Torus.p101
    ∷ kernel Torus.p110
    ∷ kernel Torus.p111
    ∷ Torus.character left Torus.p000
    ∷ Torus.character left Torus.p001
    ∷ Torus.character left Torus.p010
    ∷ Torus.character left Torus.p011
    ∷ Torus.character left Torus.p100
    ∷ Torus.character left Torus.p101
    ∷ Torus.character left Torus.p110
    ∷ Torus.character left Torus.p111
    ∷ Torus.character right Torus.p000
    ∷ Torus.character right Torus.p001
    ∷ Torus.character right Torus.p010
    ∷ Torus.character right Torus.p011
    ∷ Torus.character right Torus.p100
    ∷ Torus.character right Torus.p101
    ∷ Torus.character right Torus.p110
    ∷ Torus.character right Torus.p111
    ∷ []
    )

pairMultiplierSymmetric :
  (kernel : Torus.BitTorus3 → ℚ) →
  (left right : Torus.BitTorus3) →
  pairMultiplier kernel left right
  ≡ pairMultiplier kernel right left
pairMultiplierSymmetric kernel left right
  rewrite addPointCommutative left right =
  solve
    ( kernelTransform kernel (Torus.addPoint right left)
    ∷ kernelTransform kernel left
    ∷ kernelTransform kernel right
    ∷ kernelTransform kernel Torus.zeroMode
    ∷ []
    )

pairMultiplierLeftZero :
  (kernel : Torus.BitTorus3 → ℚ) →
  (right : Torus.BitTorus3) →
  pairMultiplier kernel Torus.zeroMode right ≡ 0ℚ
pairMultiplierLeftZero kernel right
  rewrite addZeroLeft right =
  solve
    ( kernelTransform kernel right
    ∷ kernelTransform kernel Torus.zeroMode
    ∷ []
    )

pairMultiplierRightZero :
  (kernel : Torus.BitTorus3 → ℚ) →
  (left : Torus.BitTorus3) →
  pairMultiplier kernel left Torus.zeroMode ≡ 0ℚ
pairMultiplierRightZero kernel left
  rewrite addZeroRight left =
  solve
    ( kernelTransform kernel left
    ∷ kernelTransform kernel Torus.zeroMode
    ∷ []
    )

rationalConjugate : ℚ → ℚ
rationalConjugate value = value

negateMode : Torus.BitTorus3 → Torus.BitTorus3
negateMode mode = mode

kernelTransformNegateConjugate :
  (kernel : Torus.BitTorus3 → ℚ) →
  (mode : Torus.BitTorus3) →
  kernelTransform kernel (negateMode mode)
  ≡ rationalConjugate (kernelTransform kernel mode)
kernelTransformNegateConjugate kernel mode = refl
