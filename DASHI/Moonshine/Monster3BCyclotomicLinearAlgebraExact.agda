module DASHI.Moonshine.Monster3BCyclotomicLinearAlgebraExact where

------------------------------------------------------------------------
-- EXACT LINEAR ALGEBRA ON Q(zeta_3) NEEDED BY FINITE FOURIER PROJECTORS
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C3

add : C3.Cyclotomic3 → C3.Cyclotomic3 → C3.Cyclotomic3
add (C3.cyclotomic3 a b) (C3.cyclotomic3 c d) =
  C3.cyclotomic3 (a + c) (b + d)

negate : C3.Cyclotomic3 → C3.Cyclotomic3
negate (C3.cyclotomic3 a b) = C3.cyclotomic3 (- a) (- b)

scale : ℚ → C3.Cyclotomic3 → C3.Cyclotomic3
scale r (C3.cyclotomic3 a b) = C3.cyclotomic3 (r * a) (r * b)

three : C3.Cyclotomic3
three = add C3.one (add C3.one C3.one)

zetaSumZero : add C3.one (add C3.zeta C3.zetaSquared) ≡ C3.zero
zetaSumZero = C3.cyclotomic3Ext step1 step2
  where
    step1 : 1ℚ + (0ℚ + - 1ℚ) ≡ 0ℚ
    step1 = solve []
    step2 : 0ℚ + (1ℚ + - 1ℚ) ≡ 0ℚ
    step2 = solve []

addAssociative : (a b c : C3.Cyclotomic3) →
  add (add a b) c ≡ add a (add b c)
addAssociative (C3.cyclotomic3 a b) (C3.cyclotomic3 c d)
  (C3.cyclotomic3 e f) =
  C3.cyclotomic3Ext step1 step2
  where
    step1 : (a + c) + e ≡ a + (c + e)
    step1 = solve (a ∷ c ∷ e ∷ [])
    step2 : (b + d) + f ≡ b + (d + f)
    step2 = solve (b ∷ d ∷ f ∷ [])

addCommutative : (a b : C3.Cyclotomic3) → add a b ≡ add b a
addCommutative (C3.cyclotomic3 a b) (C3.cyclotomic3 c d) =
  C3.cyclotomic3Ext step1 step2
  where
    step1 : a + c ≡ c + a
    step1 = solve (a ∷ c ∷ [])
    step2 : b + d ≡ d + b
    step2 = solve (b ∷ d ∷ [])

multiplyCommutative : (a b : C3.Cyclotomic3) →
  C3.multiply a b ≡ C3.multiply b a
multiplyCommutative
  (C3.cyclotomic3 a b) (C3.cyclotomic3 c d) =
  C3.cyclotomic3Ext step1 step2
  where
    step1 : a * c - b * d ≡ c * a - d * b
    step1 = solve (a ∷ b ∷ c ∷ d ∷ [])
    step2 : a * d + b * c - b * d ≡ c * b + d * a - d * b
    step2 = solve (a ∷ b ∷ c ∷ d ∷ [])

multiplyDistributesOverAddLeft : (a b c : C3.Cyclotomic3) →
  C3.multiply a (add b c) ≡ add (C3.multiply a b) (C3.multiply a c)
multiplyDistributesOverAddLeft
  (C3.cyclotomic3 a b) (C3.cyclotomic3 c d) (C3.cyclotomic3 e f) =
  C3.cyclotomic3Ext step1 step2
  where
    step1 : a * (c + e) - b * (d + f) ≡ (a * c - b * d) + (a * e - b * f)
    step1 = solve (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ [])
    step2 : a * (d + f) + b * (c + e) - b * (d + f) ≡ (a * d + b * c - b * d) + (a * f + b * e - b * f)
    step2 = solve (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ [])

multiplyDistributesOverAddRight : (a b c : C3.Cyclotomic3) →
  C3.multiply (add a b) c ≡ add (C3.multiply a c) (C3.multiply b c)
multiplyDistributesOverAddRight
  (C3.cyclotomic3 a b) (C3.cyclotomic3 c d) (C3.cyclotomic3 e f) =
  C3.cyclotomic3Ext step1 step2
  where
    step1 : (a + c) * e - (b + d) * f ≡ (a * e - b * f) + (c * e - d * f)
    step1 = solve (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ [])
    step2 : (a + c) * f + (b + d) * e - (b + d) * f ≡ (a * f + b * e - b * f) + (c * f + d * e - d * f)
    step2 = solve (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ [])

multiplyScaleLeft :
  (r : ℚ) → (a b : C3.Cyclotomic3) →
  C3.multiply (scale r a) b ≡ scale r (C3.multiply a b)
multiplyScaleLeft r
  (C3.cyclotomic3 a b) (C3.cyclotomic3 c d) =
  C3.cyclotomic3Ext step1 step2
  where
    step1 : (r * a) * c - (r * b) * d ≡ r * (a * c - b * d)
    step1 = solve (r ∷ a ∷ b ∷ c ∷ d ∷ [])
    step2 : (r * a) * d + (r * b) * c - (r * b) * d ≡ r * (a * d + b * c - b * d)
    step2 = solve (r ∷ a ∷ b ∷ c ∷ d ∷ [])

multiplyScaleRight :
  (r : ℚ) → (a b : C3.Cyclotomic3) →
  C3.multiply a (scale r b) ≡ scale r (C3.multiply a b)
multiplyScaleRight r
  (C3.cyclotomic3 a b) (C3.cyclotomic3 c d) =
  C3.cyclotomic3Ext step1 step2
  where
    step1 : a * (r * c) - b * (r * d) ≡ r * (a * c - b * d)
    step1 = solve (r ∷ a ∷ b ∷ c ∷ d ∷ [])
    step2 : a * (r * d) + b * (r * c) - b * (r * d) ≡ r * (a * d + b * c - b * d)
    step2 = solve (r ∷ a ∷ b ∷ c ∷ d ∷ [])

scaleScale :
  (r s : ℚ) → (a : C3.Cyclotomic3) →
  scale r (scale s a) ≡ scale (r * s) a
scaleScale r s (C3.cyclotomic3 a b) =
  C3.cyclotomic3Ext step1 step2
  where
    step1 : r * (s * a) ≡ (r * s) * a
    step1 = solve (r ∷ s ∷ a ∷ [])
    step2 : r * (s * b) ≡ (r * s) * b
    step2 = solve (r ∷ s ∷ b ∷ [])

oneActsLeft : (a : C3.Cyclotomic3) → C3.multiply C3.one a ≡ a
oneActsLeft (C3.cyclotomic3 a b) =
  C3.cyclotomic3Ext step1 step2
  where
    step1 : 1ℚ * a - 0ℚ * b ≡ a
    step1 = solve (a ∷ b ∷ [])
    step2 : 1ℚ * b + 0ℚ * a - 0ℚ * b ≡ b
    step2 = solve (a ∷ b ∷ [])

zeroActsLeft : (a : C3.Cyclotomic3) → C3.multiply C3.zero a ≡ C3.zero
zeroActsLeft (C3.cyclotomic3 a b) =
  C3.cyclotomic3Ext step1 step2
  where
    step1 : 0ℚ * a - 0ℚ * b ≡ 0ℚ
    step1 = solve (a ∷ b ∷ [])
    step2 : 0ℚ * b + 0ℚ * a - 0ℚ * b ≡ 0ℚ
    step2 = solve (a ∷ b ∷ [])

zetaSquaredTimesZetaSquaredIsZeta :
  C3.multiply C3.zetaSquared C3.zetaSquared ≡ C3.zeta
zetaSquaredTimesZetaSquaredIsZeta =
  C3.cyclotomic3Ext step1 step2
  where
    step1 : (- 1ℚ) * (- 1ℚ) - (- 1ℚ) * (- 1ℚ) ≡ 0ℚ
    step1 = solve []
    step2 : (- 1ℚ) * (- 1ℚ) + (- 1ℚ) * (- 1ℚ) - (- 1ℚ) * (- 1ℚ) ≡ 1ℚ
    step2 = solve []

phaseCycleSumOnOne :
  add C3.one (add C3.zeta C3.zetaSquared) ≡ C3.zero
phaseCycleSumOnOne = zetaSumZero

phaseCycleSumTimes : (a : C3.Cyclotomic3) →
  add
    (C3.multiply C3.one a)
    (add (C3.multiply C3.zeta a) (C3.multiply C3.zetaSquared a))
  ≡ C3.zero
phaseCycleSumTimes (C3.cyclotomic3 a b) =
  C3.cyclotomic3Ext step1 step2
  where
    step1 : (1ℚ * a - 0ℚ * b) + ((0ℚ * a - 1ℚ * b) + ((- 1ℚ) * a - (- 1ℚ) * b)) ≡ 0ℚ
    step1 = solve (a ∷ b ∷ [])
    step2 : (1ℚ * b + 0ℚ * a - 0ℚ * b) + ((0ℚ * b + 1ℚ * a - 1ℚ * b) + ((- 1ℚ) * b + (- 1ℚ) * a - (- 1ℚ) * b)) ≡ 0ℚ
    step2 = solve (a ∷ b ∷ [])

threeTimes : (a : C3.Cyclotomic3) →
  add a (add a a) ≡ scale (1ℚ + (1ℚ + 1ℚ)) a
threeTimes (C3.cyclotomic3 a b) =
  C3.cyclotomic3Ext step1 step2
  where
    step1 : a + (a + a) ≡ (1ℚ + (1ℚ + 1ℚ)) * a
    step1 = solve (a ∷ [])
    step2 : b + (b + b) ≡ (1ℚ + (1ℚ + 1ℚ)) * b
    step2 = solve (b ∷ [])
