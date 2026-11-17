module DASHI.Moonshine.Monster3BCyclotomicLinearAlgebraExact where

------------------------------------------------------------------------
-- EXACT LINEAR ALGEBRA ON Q(zeta_3) NEEDED BY FINITE FOURIER PROJECTORS
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

import Data.Rational.Properties as ℚP

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
zetaSumZero = refl

addAssociative : (a b c : C3.Cyclotomic3) →
  add (add a b) c ≡ add a (add b c)
addAssociative (C3.cyclotomic3 a b) (C3.cyclotomic3 c d)
  (C3.cyclotomic3 e f) =
  C3.cyclotomic3Ext
    (ℚP.+-assoc a c e)
    (ℚP.+-assoc b d f)

addCommutative : (a b : C3.Cyclotomic3) → add a b ≡ add b a
addCommutative (C3.cyclotomic3 a b) (C3.cyclotomic3 c d) =
  C3.cyclotomic3Ext (ℚP.+-comm a c) (ℚP.+-comm b d)

multiplyCommutative : (a b : C3.Cyclotomic3) →
  C3.multiply a b ≡ C3.multiply b a
multiplyCommutative
  (C3.cyclotomic3 a b) (C3.cyclotomic3 c d) =
  C3.cyclotomic3Ext commStep1 commStep2
  where
    commStep1 : (a * c - b * d) ≡ (c * a - d * b)
    commStep1 = solve (a ∷ b ∷ c ∷ d ∷ [])

    commStep2 : (a * d + b * c - b * d) ≡ (c * b + d * a - d * b)
    commStep2 = solve (a ∷ b ∷ c ∷ d ∷ [])

multiplyDistributesOverAddLeft : (a b c : C3.Cyclotomic3) →
  C3.multiply a (add b c) ≡ add (C3.multiply a b) (C3.multiply a c)
multiplyDistributesOverAddLeft
  (C3.cyclotomic3 a b) (C3.cyclotomic3 c d) (C3.cyclotomic3 e f) =
  C3.cyclotomic3Ext distLeftStep1 distLeftStep2
  where
    distLeftStep1 : a * (c + e) - b * (d + f) ≡ (a * c - b * d) + (a * e - b * f)
    distLeftStep1 = solve (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ [])

    distLeftStep2 : a * (d + f) + b * (c + e) - b * (d + f) ≡ (a * d + b * c - b * d) + (a * f + b * e - b * f)
    distLeftStep2 = solve (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ [])

multiplyDistributesOverAddRight : (a b c : C3.Cyclotomic3) →
  C3.multiply (add a b) c ≡ add (C3.multiply a c) (C3.multiply b c)
multiplyDistributesOverAddRight
  (C3.cyclotomic3 a b) (C3.cyclotomic3 c d) (C3.cyclotomic3 e f) =
  C3.cyclotomic3Ext distRightStep1 distRightStep2
  where
    distRightStep1 : (a + c) * e - (b + d) * f ≡ (a * e - b * f) + (c * e - d * f)
    distRightStep1 = solve (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ [])

    distRightStep2 : (a + c) * f + (b + d) * e - (b + d) * f ≡ (a * f + b * e - b * f) + (c * f + d * e - d * f)
    distRightStep2 = solve (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ [])

multiplyScaleLeft :
  (r : ℚ) → (a b : C3.Cyclotomic3) →
  C3.multiply (scale r a) b ≡ scale r (C3.multiply a b)
multiplyScaleLeft r
  (C3.cyclotomic3 a b) (C3.cyclotomic3 c d) =
  C3.cyclotomic3Ext scaleLeftStep1 scaleLeftStep2
  where
    scaleLeftStep1 : (r * a) * c - (r * b) * d ≡ r * (a * c - b * d)
    scaleLeftStep1 = solve (r ∷ a ∷ b ∷ c ∷ d ∷ [])

    scaleLeftStep2 : (r * a) * d + (r * b) * c - (r * b) * d ≡ r * (a * d + b * c - b * d)
    scaleLeftStep2 = solve (r ∷ a ∷ b ∷ c ∷ d ∷ [])

multiplyScaleRight :
  (r : ℚ) → (a b : C3.Cyclotomic3) →
  C3.multiply a (scale r b) ≡ scale r (C3.multiply a b)
multiplyScaleRight r
  (C3.cyclotomic3 a b) (C3.cyclotomic3 c d) =
  C3.cyclotomic3Ext scaleRightStep1 scaleRightStep2
  where
    scaleRightStep1 : a * (r * c) - b * (r * d) ≡ r * (a * c - b * d)
    scaleRightStep1 = solve (r ∷ a ∷ b ∷ c ∷ d ∷ [])

    scaleRightStep2 : a * (r * d) + b * (r * c) - b * (r * d) ≡ r * (a * d + b * c - b * d)
    scaleRightStep2 = solve (r ∷ a ∷ b ∷ c ∷ d ∷ [])

scaleScale :
  (r s : ℚ) → (a : C3.Cyclotomic3) →
  scale r (scale s a) ≡ scale (r * s) a
scaleScale r s (C3.cyclotomic3 a b) =
  C3.cyclotomic3Ext scaleScaleStep1 scaleScaleStep2
  where
    scaleScaleStep1 : r * (s * a) ≡ (r * s) * a
    scaleScaleStep1 = solve (r ∷ s ∷ a ∷ [])

    scaleScaleStep2 : r * (s * b) ≡ (r * s) * b
    scaleScaleStep2 = solve (r ∷ s ∷ b ∷ [])

oneActsLeft : (a : C3.Cyclotomic3) → C3.multiply C3.one a ≡ a
oneActsLeft (C3.cyclotomic3 a b) =
  C3.cyclotomic3Ext oneActsStep1 oneActsStep2
  where
    oneActsStep1 : 1ℚ * a - 0ℚ * b ≡ a
    oneActsStep1 = solve (a ∷ b ∷ [])

    oneActsStep2 : 1ℚ * b + 0ℚ * a - 0ℚ * b ≡ b
    oneActsStep2 = solve (a ∷ b ∷ [])

zeroActsLeft : (a : C3.Cyclotomic3) → C3.multiply C3.zero a ≡ C3.zero
zeroActsLeft (C3.cyclotomic3 a b) =
  C3.cyclotomic3Ext zeroActsStep1 zeroActsStep2
  where
    zeroActsStep1 : 0ℚ * a - 0ℚ * b ≡ 0ℚ
    zeroActsStep1 = solve (a ∷ b ∷ [])

    zeroActsStep2 : 0ℚ * b + 0ℚ * a - 0ℚ * b ≡ 0ℚ
    zeroActsStep2 = solve (a ∷ b ∷ [])

zetaSquaredTimesZetaSquaredIsZeta :
  C3.multiply C3.zetaSquared C3.zetaSquared ≡ C3.zeta
zetaSquaredTimesZetaSquaredIsZeta =
  C3.cyclotomic3Ext zetaSqStep1 zetaSqStep2
  where
    zetaSqStep1 : (- 1ℚ) * (- 1ℚ) - (- 1ℚ) * (- 1ℚ) ≡ 0ℚ
    zetaSqStep1 = refl

    zetaSqStep2 : (- 1ℚ) * (- 1ℚ) + (- 1ℚ) * (- 1ℚ) - (- 1ℚ) * (- 1ℚ) ≡ 1ℚ
    zetaSqStep2 = refl

phaseCycleSumOnOne :
  add C3.one (add C3.zeta C3.zetaSquared) ≡ C3.zero
phaseCycleSumOnOne = zetaSumZero

phaseCycleSumTimes : (a : C3.Cyclotomic3) →
  add
    (C3.multiply C3.one a)
    (add (C3.multiply C3.zeta a) (C3.multiply C3.zetaSquared a))
  ≡ C3.zero
phaseCycleSumTimes (C3.cyclotomic3 a b) =
  C3.cyclotomic3Ext phaseCycleStep1 phaseCycleStep2
  where
    phaseCycleStep1 : (1ℚ * a - 0ℚ * b) + ((0ℚ * a - 1ℚ * b) + ((- 1ℚ) * a - (- 1ℚ) * b)) ≡ 0ℚ
    phaseCycleStep1 = solve (a ∷ b ∷ [])

    phaseCycleStep2 : (1ℚ * b + 0ℚ * a - 0ℚ * b) + ((0ℚ * b + 1ℚ * a - 1ℚ * b) + (((- 1ℚ) * b + (- 1ℚ) * a) - (- 1ℚ) * b)) ≡ 0ℚ
    phaseCycleStep2 = solve (a ∷ b ∷ [])

threeTimes : (a : C3.Cyclotomic3) →
  add a (add a a) ≡ scale (1ℚ + (1ℚ + 1ℚ)) a
threeTimes (C3.cyclotomic3 a b) =
  C3.cyclotomic3Ext threeTimesStep1 threeTimesStep2
  where
    threeTimesStep1 : a + (a + a) ≡ (1ℚ + (1ℚ + 1ℚ)) * a
    threeTimesStep1 = solve (a ∷ [])

    threeTimesStep2 : b + (b + b) ≡ (1ℚ + (1ℚ + 1ℚ)) * b
    threeTimesStep2 = solve (b ∷ [])
