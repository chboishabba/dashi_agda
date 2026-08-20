module DASHI.Physics.Closure.NSTriadKNHeterochiralReverseTriangleRound105Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- ROUND105 / REVERSE-TRIANGLE MINORITY-RADIUS GAIN
--
-- Round102 reduced every mixed-helicity critical-production class to
--
--   +/- 2 r_m (r_a-r_b) A,
--
-- where r_m is the unique minority-helicity radius and r_a,r_b are the two
-- majority radii.  It explicitly left the resonant reverse-triangle estimate
-- as the next metric step.
--
-- For a resonant Fourier triad the radii form a triangle.  Algebraically the
-- two triangle inequalities
--
--   r_a <= r_b + r_m,
--   r_b <= r_a + r_m
--
-- are exactly equivalent to
--
--   r_a-r_b <= r_m,
--   r_b-r_a <= r_m.
--
-- Thus the majority-radius difference costs at most ONE minority radius.
-- This file proves all three cyclic versions over exact rationals and also the
-- corresponding oriented coefficient-square gain without invoking a square
-- root or floating-point norm.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

record TriangleRadii : Set where
  constructor triangle-radii
  field
    radiusK radiusP radiusQ : ℚ
    radiusKNonnegative : 0ℚ ≤ radiusK
    radiusPNonnegative : 0ℚ ≤ radiusP
    radiusQNonnegative : 0ℚ ≤ radiusQ

    kBelowPPlusQ : radiusK ≤ radiusP + radiusQ
    pBelowKPlusQ : radiusP ≤ radiusK + radiusQ
    qBelowKPlusP : radiusQ ≤ radiusK + radiusP

open TriangleRadii public

two : ℚ
two = Int.+ 2 / 1

twoNonnegative : 0ℚ ≤ two
twoNonnegative = ℚP.<⇒≤ (ℚP.positive⁻¹ two)

qMinusPBelowK : (T : TriangleRadii) → radiusQ T - radiusP T ≤ radiusK T
qMinusPBelowK T =
  let
    shifted : radiusQ T + (0ℚ - radiusP T)
      ≤ (radiusK T + radiusP T) + (0ℚ - radiusP T)
    shifted = ℚP.+-mono-≤ (qBelowKPlusP T) ℚP.≤-refl

    leftMeaning : radiusQ T + (0ℚ - radiusP T) ≡ radiusQ T - radiusP T
    leftMeaning = solve (radiusQ T ∷ radiusP T ∷ [])

    rightMeaning :
      (radiusK T + radiusP T) + (0ℚ - radiusP T) ≡ radiusK T
    rightMeaning = solve (radiusK T ∷ radiusP T ∷ [])
  in
  subst
    (λ left → left ≤ radiusK T)
    leftMeaning
    (subst
      (λ right → radiusQ T + (0ℚ - radiusP T) ≤ right)
      rightMeaning shifted)

pMinusQBelowK : (T : TriangleRadii) → radiusP T - radiusQ T ≤ radiusK T
pMinusQBelowK T =
  let
    shifted : radiusP T + (0ℚ - radiusQ T)
      ≤ (radiusK T + radiusQ T) + (0ℚ - radiusQ T)
    shifted = ℚP.+-mono-≤ (pBelowKPlusQ T) ℚP.≤-refl
  in
  subst
    (λ left → left ≤ radiusK T)
    (solve (radiusP T ∷ radiusQ T ∷ []))
    (subst
      (λ right → radiusP T + (0ℚ - radiusQ T) ≤ right)
      (solve (radiusK T ∷ radiusQ T ∷ []))
      shifted)

kMinusQBelowP : (T : TriangleRadii) → radiusK T - radiusQ T ≤ radiusP T
kMinusQBelowP T =
  let shifted = ℚP.+-mono-≤ (kBelowPPlusQ T) ℚP.≤-refl
  in
  subst
    (λ left → left ≤ radiusP T)
    (solve (radiusK T ∷ radiusQ T ∷ []))
    (subst
      (λ right → radiusK T + (0ℚ - radiusQ T) ≤ right)
      (solve (radiusP T ∷ radiusQ T ∷ []))
      shifted)

qMinusKBelowP : (T : TriangleRadii) → radiusQ T - radiusK T ≤ radiusP T
qMinusKBelowP T =
  let shifted = ℚP.+-mono-≤ (qBelowKPlusP T) ℚP.≤-refl
  in
  subst
    (λ left → left ≤ radiusP T)
    (solve (radiusQ T ∷ radiusK T ∷ []))
    (subst
      (λ right → radiusQ T + (0ℚ - radiusK T) ≤ right)
      (solve (radiusP T ∷ radiusK T ∷ []))
      shifted)

pMinusKBelowQ : (T : TriangleRadii) → radiusP T - radiusK T ≤ radiusQ T
pMinusKBelowQ T =
  let shifted = ℚP.+-mono-≤ (pBelowKPlusQ T) ℚP.≤-refl
  in
  subst
    (λ left → left ≤ radiusQ T)
    (solve (radiusP T ∷ radiusK T ∷ []))
    (subst
      (λ right → radiusP T + (0ℚ - radiusK T) ≤ right)
      (solve (radiusQ T ∷ radiusK T ∷ []))
      shifted)

kMinusPBelowQ : (T : TriangleRadii) → radiusK T - radiusP T ≤ radiusQ T
kMinusPBelowQ T =
  let shifted = ℚP.+-mono-≤ (kBelowPPlusQ T) ℚP.≤-refl
  in
  subst
    (λ left → left ≤ radiusQ T)
    (solve (radiusK T ∷ radiusP T ∷ []))
    (subst
      (λ right → radiusK T + (0ℚ - radiusP T) ≤ right)
      (solve (radiusQ T ∷ radiusP T ∷ []))
      shifted)

-- Oriented adverse coefficient bound for minority k.  If q>=p, the positive
-- radial difference is q-p and the critical coefficient is 2 k (q-p).
minorityKOrientedCoefficientBelowTwoKSquared :
  (T : TriangleRadii) →
  0ℚ ≤ radiusQ T - radiusP T →
  two * radiusK T * (radiusQ T - radiusP T)
  ≤ two * radiusK T * radiusK T
minorityKOrientedCoefficientBelowTwoKSquared T differenceNN =
  let
    twoKNN : 0ℚ ≤ two * radiusK T
    twoKNN =
      let
        instance twoNN = nonNegative twoNonnegative
        instance kNN = nonNegative (radiusKNonnegative T)
      in ℚP.nonNegative⁻¹ (two * radiusK T)
  in
  let instance coefficientNN = nonNegative twoKNN
  in ℚP.*-monoˡ-≤-nonNeg
      (two * radiusK T)
      (qMinusPBelowK T)

minorityPOrientedCoefficientBelowTwoPSquared :
  (T : TriangleRadii) →
  0ℚ ≤ radiusK T - radiusQ T →
  two * radiusP T * (radiusK T - radiusQ T)
  ≤ two * radiusP T * radiusP T
minorityPOrientedCoefficientBelowTwoPSquared T differenceNN =
  let
    twoPNN : 0ℚ ≤ two * radiusP T
    twoPNN =
      let
        instance twoNN = nonNegative twoNonnegative
        instance pNN = nonNegative (radiusPNonnegative T)
      in ℚP.nonNegative⁻¹ (two * radiusP T)
  in
  let instance coefficientNN = nonNegative twoPNN
  in ℚP.*-monoˡ-≤-nonNeg
      (two * radiusP T)
      (kMinusQBelowP T)

minorityQOrientedCoefficientBelowTwoQSquared :
  (T : TriangleRadii) →
  0ℚ ≤ radiusP T - radiusK T →
  two * radiusQ T * (radiusP T - radiusK T)
  ≤ two * radiusQ T * radiusQ T
minorityQOrientedCoefficientBelowTwoQSquared T differenceNN =
  let
    twoQNN : 0ℚ ≤ two * radiusQ T
    twoQNN =
      let
        instance twoNN = nonNegative twoNonnegative
        instance qNN = nonNegative (radiusQNonnegative T)
      in ℚP.nonNegative⁻¹ (two * radiusQ T)
  in
  let instance coefficientNN = nonNegative twoQNN
  in ℚP.*-monoˡ-≤-nonNeg
      (two * radiusQ T)
      (pMinusKBelowQ T)

round105ReverseTriangleMinorityGainClosed : Bool
round105ReverseTriangleMinorityGainClosed = true

round105MixedHelicityFrequencyCoefficientCostsMinoritySquare : Bool
round105MixedHelicityFrequencyCoefficientCostsMinoritySquare = true

round105ReverseTriangleMinorityGainClosedIsTrue :
  round105ReverseTriangleMinorityGainClosed ≡ true
round105ReverseTriangleMinorityGainClosedIsTrue = refl

round105MixedHelicityFrequencyCoefficientCostsMinoritySquareIsTrue :
  round105MixedHelicityFrequencyCoefficientCostsMinoritySquare ≡ true
round105MixedHelicityFrequencyCoefficientCostsMinoritySquareIsTrue = refl
