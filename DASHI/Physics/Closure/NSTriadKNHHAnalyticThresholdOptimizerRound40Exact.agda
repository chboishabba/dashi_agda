module DASHI.Physics.Closure.NSTriadKNHHAnalyticThresholdOptimizerRound40Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- If the physical HH-good/HH-bad taxes take the natural complementary form
--
--   eta_good(delta) = A sqrt(delta),
--   eta_bad(delta)  = B / delta,
--
-- write delta = r^2 and carry r together with its exact rational inverse.
-- Then
--
--   f(r) = A r + B r^{-2}.
--
-- This module avoids calculus and irrational cube roots.  It proves directly
-- over Q that any positive rational r satisfying the balance certificate
--
--   A r^3 = 2 B
--
-- is a *global* minimizer among all positive rational scales.  The proof is
-- the exact factorization
--
--   2 x^2 (f(x)-f(r))
--     = A (x-r)^2 (2x+r) >= 0.
--
-- Thus when the physical constants admit an exact rational balanced scale,
-- the Round-39 generic threshold optimizer can be replaced by a transparent
-- symbolic certificate.  If they do not, the generic certified minimizer is
-- still the correct fallback.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _+_; _*_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_; _<?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold

half two three : ℚ
half = Int.+ 1 / 2
two = Int.+ 2 / 1
three = Int.+ 3 / 1

halfNonnegative : 0ℚ ≤ half
halfNonnegative = toWitness {a? = 0ℚ ≤? half} _

twoNonnegative : 0ℚ ≤ two
twoNonnegative = toWitness {a? = 0ℚ ≤? two} _

mulNonnegative : ∀ {left right : ℚ} →
  0ℚ ≤ left → 0ℚ ≤ right → 0ℚ ≤ left * right
mulNonnegative {left} {right} leftNN rightNN =
  let
    instance
      leftNNI = nonNegative leftNN
      rightNNI = nonNegative rightNN
      productNNI = ℚP.nonNeg*nonNeg⇒nonNeg left right
  in
  ℚP.nonNegative⁻¹ (left * right)

scaleValue scaleInverse : Threshold.PositiveThreshold → ℚ
scaleValue = Threshold.threshold
scaleInverse = Threshold.thresholdInverse

hhGoodTax : ℚ → Threshold.PositiveThreshold → ℚ
hhGoodTax A scale = A * scaleValue scale

hhBadTax : ℚ → Threshold.PositiveThreshold → ℚ
hhBadTax B scale = B * scaleInverse scale * scaleInverse scale

combinedHHTax : ℚ → ℚ → Threshold.PositiveThreshold → ℚ
combinedHHTax A B scale = hhGoodTax A scale + hhBadTax B scale

record BalancedHHThreshold
    (A B : ℚ) : Set where
  constructor balanced-hh-threshold
  field
    selectedScale : Threshold.PositiveThreshold
    A-nonnegative : 0ℚ ≤ A
    B-nonnegative : 0ℚ ≤ B
    cubicBalance :
      A * scaleValue selectedScale
        * scaleValue selectedScale
        * scaleValue selectedScale
      ≡ two * B

open BalancedHHThreshold public

balanceSolvesBadTax :
  ∀ {A B}
    (balance : BalancedHHThreshold A B) →
  hhBadTax B (selectedScale balance)
  ≡ half * A * scaleValue (selectedScale balance)
balanceSolvesBadTax {A} {B} balance =
  let
    r = scaleValue (selectedScale balance)
    rinv = scaleInverse (selectedScale balance)

    scaledBalance :
      half * (A * r * r * r) * rinv * rinv
      ≡ half * (two * B) * rinv * rinv
    scaledBalance =
      cong (λ value → half * value * rinv * rinv)
        (cubicBalance balance)

    leftFactor :
      half * (A * r * r * r) * rinv * rinv
      ≡ half * A * r * ((rinv * r) * (rinv * r))
    leftFactor = solve (A ∷ r ∷ rinv ∷ [])

    leftNormalize :
      half * A * r * ((rinv * r) * (rinv * r))
      ≡ half * A * r
    leftNormalize
      rewrite Threshold.inverseMeaning (selectedScale balance) =
      solve (A ∷ r ∷ [])

    rightNormalize :
      half * (two * B) * rinv * rinv
      ≡ hhBadTax B (selectedScale balance)
    rightNormalize = solve (B ∷ rinv ∷ [])
  in
  trans
    (sym rightNormalize)
    (trans
      (sym scaledBalance)
      (trans leftFactor leftNormalize))

selectedTaxClosedForm :
  ∀ {A B}
    (balance : BalancedHHThreshold A B) →
  combinedHHTax A B (selectedScale balance)
  ≡ three * half * A * scaleValue (selectedScale balance)
selectedTaxClosedForm {A} {B} balance
  rewrite balanceSolvesBadTax balance =
  solve (A ∷ scaleValue (selectedScale balance) ∷ [])

candidateScaledTax :
  ∀ A B (candidate : Threshold.PositiveThreshold) →
  scaleValue candidate * scaleValue candidate
    * combinedHHTax A B candidate
  ≡ A * scaleValue candidate * scaleValue candidate * scaleValue candidate + B
candidateScaledTax A B candidate =
  let
    x = scaleValue candidate
    xinv = scaleInverse candidate

    factor :
      x * x * (A * x + B * xinv * xinv)
      ≡ A * x * x * x + B * ((xinv * x) * (xinv * x))
    factor = solve (A ∷ B ∷ x ∷ xinv ∷ [])

    normalize :
      A * x * x * x + B * ((xinv * x) * (xinv * x))
      ≡ A * x * x * x + B
    normalize
      rewrite Threshold.inverseMeaning candidate =
      solve (A ∷ B ∷ x ∷ [])
  in
  trans factor normalize

balanceSolvesB :
  ∀ {A B}
    (balance : BalancedHHThreshold A B) →
  B ≡ half * A
      * scaleValue (selectedScale balance)
      * scaleValue (selectedScale balance)
      * scaleValue (selectedScale balance)
balanceSolvesB {A} {B} balance =
  let r = scaleValue (selectedScale balance)
      scaled = cong (half *_) (cubicBalance balance)
      leftMeaning : half * (A * r * r * r)
        ≡ half * A * r * r * r
      leftMeaning = solve (A ∷ r ∷ [])
      rightMeaning : half * (two * B) ≡ B
      rightMeaning = solve (B ∷ [])
  in
  trans (sym rightMeaning) (trans (sym scaled) leftMeaning)

factorizedGapNonnegative :
  ∀ {A B}
    (balance : BalancedHHThreshold A B) →
    (candidate : Threshold.PositiveThreshold) →
  0ℚ ≤
    half * A
      * L2.square
          (scaleValue candidate - scaleValue (selectedScale balance))
      * (two * scaleValue candidate + scaleValue (selectedScale balance))
factorizedGapNonnegative {A} balance candidate =
  let
    x = scaleValue candidate
    r = scaleValue (selectedScale balance)
    xNN = Threshold.thresholdNonnegative candidate
    rNN = Threshold.thresholdNonnegative (selectedScale balance)
    twoXNN = mulNonnegative twoNonnegative xNN
    sumNN = L2.addNonnegative twoXNN rNN
    squareNN = L2.squareNonnegative (x - r)
  in
  mulNonnegative
    (mulNonnegative
      (mulNonnegative halfNonnegative (A-nonnegative balance))
      squareNN)
    sumNN

scaledSelectedBelowScaledCandidate :
  ∀ {A B}
    (balance : BalancedHHThreshold A B) →
    (candidate : Threshold.PositiveThreshold) →
  scaleValue candidate * scaleValue candidate
    * combinedHHTax A B (selectedScale balance)
  ≤
  scaleValue candidate * scaleValue candidate
    * combinedHHTax A B candidate
scaledSelectedBelowScaledCandidate {A} {B} balance candidate =
  let
    x = scaleValue candidate
    r = scaleValue (selectedScale balance)
    selected = combinedHHTax A B (selectedScale balance)
    candidateTax = combinedHHTax A B candidate
    gap =
      half * A * L2.square (x - r) * (two * x + r)

    gapNN : 0ℚ ≤ gap
    gapNN = factorizedGapNonnegative balance candidate

    base : x * x * selected + 0ℚ ≤ x * x * selected + gap
    base = ℚP.+-monoʳ-≤ (x * x * selected) gapNN

    leftMeaning : x * x * selected + 0ℚ ≡ x * x * selected
    leftMeaning = solve (x ∷ selected ∷ [])

    rightStep :
      x * x * selected + gap
      ≡ A * x * x * x + B
    rightStep
      rewrite selectedTaxClosedForm balance
            | balanceSolvesB balance =
      solve (A ∷ x ∷ r ∷ [])

    candidateMeaning :
      x * x * candidateTax ≡ A * x * x * x + B
    candidateMeaning = candidateScaledTax A B candidate
  in
  subst
    (λ lower → lower ≤ x * x * candidateTax)
    leftMeaning
    (subst
      (λ upper → x * x * selected + 0ℚ ≤ upper)
      (trans rightStep (sym candidateMeaning))
      base)

globalBalancedThresholdMinimum :
  ∀ {A B}
    (balance : BalancedHHThreshold A B) →
    (candidate : Threshold.PositiveThreshold) →
  combinedHHTax A B (selectedScale balance)
  ≤ combinedHHTax A B candidate
globalBalancedThresholdMinimum {A} {B} balance candidate =
  let
    x = scaleValue candidate
    selected = combinedHHTax A B (selectedScale balance)
    candidateTax = combinedHHTax A B candidate

    scaled = scaledSelectedBelowScaledCandidate balance candidate

    nested :
      x * (x * selected) ≤ x * (x * candidateTax)
    nested =
      subst
        (λ lower → lower ≤ x * (x * candidateTax))
        (solve (x ∷ selected ∷ []))
        (subst
          (λ upper → x * x * selected ≤ upper)
          (solve (x ∷ candidateTax ∷ []))
          scaled)

    once : x * selected ≤ x * candidateTax
    once = Threshold.positiveThresholdCancellation
      candidate (x * selected) (x * candidateTax) nested
  in
  Threshold.positiveThresholdCancellation
    candidate selected candidateTax once

analyticHHThresholdOptimizerClosed : Bool
analyticHHThresholdOptimizerClosed = true

physicalHHConstantsFitBalancedScalingConstructed : Bool
physicalHHConstantsFitBalancedScalingConstructed = false

analyticHHThresholdOptimizerClosedIsTrue :
  analyticHHThresholdOptimizerClosed ≡ true
analyticHHThresholdOptimizerClosedIsTrue = refl
