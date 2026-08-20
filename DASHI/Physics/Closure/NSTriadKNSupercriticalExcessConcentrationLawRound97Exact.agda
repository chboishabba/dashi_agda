module DASHI.Physics.Closure.NSTriadKNSupercriticalExcessConcentrationLawRound97Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Alexey Cheskidov; Roman Shvydkoy.
-- Title: "The Regularity of Weak Solutions of the 3D Navier-Stokes
-- Equations in B^{-1}_{infinity,infinity}".
-- Archive for Rational Mechanics and Analysis 195 (2010), 159--169.
-- DOI: 10.1007/s00205-009-0265-2.
--
-- Authors: Zhen Lei; Xiao Ren.
-- Title: "Quantitative partial regularity of the Navier-Stokes equations
-- and applications".
-- arXiv:2210.01783 (2022).
-- DOI: not asserted from the supplied arXiv manuscript.
--
-- ROUND97 / EXACT CONCENTRATION BOUNDARY
--
-- The unconditional residence theorem controls how long A can remain above
-- A_*, but the Round96 open currency is D X with X=(A-A_*)_+.
--
-- On the physical positive-part realization one has 0 <= X <= A.  Combine
-- this with the squared Bernstein relation written in dissipation form
--
--   lambda * A^2 <= C_B * D.
--
-- Then, without division or square roots,
--
--   lambda * (D X)^2 <= C_B * D^3.
--
-- Thus the weighted excess is exactly a superlinear concentration problem:
-- energy/dissipation L1 control alone does not control the cubic right-hand
-- side.  Any successful occupation/escape theorem must exploit additional
-- Navier--Stokes packet dynamics, not merely the measure of the bad set.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational

square : ℚ → ℚ
square x = x * x

cube : ℚ → ℚ
cube x = x * x * x

record PhysicalExcessConcentrationCell (bernsteinConstant : ℚ) : Set where
  constructor physical-excess-concentration-cell
  field
    shellScale amplitude excess dissipation : ℚ

    bernsteinConstantNonnegative : 0ℚ ≤ bernsteinConstant
    shellScaleNonnegative : 0ℚ ≤ shellScale
    amplitudeNonnegative : 0ℚ ≤ amplitude
    excessNonnegative : 0ℚ ≤ excess
    dissipationNonnegative : 0ℚ ≤ dissipation

    excessBelowAmplitude : excess ≤ amplitude

    amplitudeSquaredBelowDissipation :
      shellScale * square amplitude ≤ bernsteinConstant * dissipation

open PhysicalExcessConcentrationCell public

excessSquareBelowAmplitudeSquare :
  ∀ {C} (cell : PhysicalExcessConcentrationCell C) →
  square (excess cell) ≤ square (amplitude cell)
excessSquareBelowAmplitudeSquare cell =
  Rational.nonnegativeProductMonotone
    (excessNonnegative cell)
    (excessNonnegative cell)
    (amplitudeNonnegative cell)
    (amplitudeNonnegative cell)
    (excessBelowAmplitude cell)
    (excessBelowAmplitude cell)

weightedExcessSquareConcentrationLaw :
  ∀ {C} (cell : PhysicalExcessConcentrationCell C) →
  shellScale cell * square (dissipation cell * excess cell)
  ≤ C * cube (dissipation cell)
weightedExcessSquareConcentrationLaw {C} cell =
  let
    lambda = shellScale cell
    A = amplitude cell
    X = excess cell
    D = dissipation cell

    x2≤a2 : square X ≤ square A
    x2≤a2 = excessSquareBelowAmplitudeSquare cell

    d2NN : 0ℚ ≤ square D
    d2NN = Rational.squareNonnegative D

    d2x2≤d2a2 : square D * square X ≤ square D * square A
    d2x2≤d2a2 =
      let instance d2NNI = nonNegative d2NN
      in ℚP.*-monoˡ-≤-nonNeg (square D) x2≤a2

    lambdaD2X2≤lambdaD2A2 :
      lambda * (square D * square X)
      ≤ lambda * (square D * square A)
    lambdaD2X2≤lambdaD2A2 =
      let instance lambdaNNI = nonNegative (shellScaleNonnegative cell)
      in ℚP.*-monoˡ-≤-nonNeg lambda d2x2≤d2a2

    d2TimesBernstein :
      square D * (lambda * square A)
      ≤ square D * (C * D)
    d2TimesBernstein =
      let instance d2NNI = nonNegative d2NN
      in ℚP.*-monoˡ-≤-nonNeg (square D)
        (amplitudeSquaredBelowDissipation cell)

    leftRearrange :
      lambda * (square D * square A)
      ≡ square D * (lambda * square A)
    leftRearrange = solve (lambda ∷ D ∷ A ∷ [])

    rightRearrange :
      square D * (C * D) ≡ C * cube D
    rightRearrange = solve (C ∷ D ∷ [])

    baseLeftToGoalRight :
      square D * (lambda * square A) ≤ C * cube D
    baseLeftToGoalRight =
      subst
        (λ right → square D * (lambda * square A) ≤ right)
        rightRearrange
        d2TimesBernstein

    middle :
      lambda * (square D * square A) ≤ C * cube D
    middle =
      subst
        (λ left → left ≤ C * cube D)
        (sym leftRearrange)
        baseLeftToGoalRight

    raw : lambda * (square D * square X) ≤ C * cube D
    raw = ℚP.≤-trans lambdaD2X2≤lambdaD2A2 middle

    interactionSquareMeaning :
      square (D * X) ≡ square D * square X
    interactionSquareMeaning = solve (D ∷ X ∷ [])
  in
  substLeft interactionSquareMeaning raw
  where
  substLeft : ∀ {a b rhs : ℚ} → a ≡ b →
    shellScale cell * b ≤ rhs → shellScale cell * a ≤ rhs
  substLeft refl hyp = hyp

round97WeightedExcessIsCubicDissipationConcentration : Bool
round97WeightedExcessIsCubicDissipationConcentration = true

round97ResidenceMeasureAloneDoesNotCloseWeightedExcess : Bool
round97ResidenceMeasureAloneDoesNotCloseWeightedExcess = true

round97WeightedExcessIsCubicDissipationConcentrationIsTrue :
  round97WeightedExcessIsCubicDissipationConcentration ≡ true
round97WeightedExcessIsCubicDissipationConcentrationIsTrue = refl
