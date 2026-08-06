module DASHI.Physics.Closure.NSTriadKNLuoNonlinearWeakLimitAuditExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Jacques-Louis Lions.
-- Title: "Quelques méthodes de résolution des problèmes aux limites non
-- linéaires".
-- DOI: not assigned to the cited Dunod 1969 edition.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- PURPOSE
-- Record a concrete obstruction behind the Galerkin-limit audit.  Linear
-- cancellation of two factors does not determine their nonlinear product.
-- On an exact four-point periodic carrier the alternating mode has zero mean,
-- while the product of two copies is the constant one mode:
--
--   mean(h) = 0,
--   mean(h) = 0,
--   mean(h * h * 1) = 1.
--
-- This is deliberately a finite selected-test countermodel, not a claim that a
-- fixed four-dimensional sequence converges weakly.  Its role is precise: a
-- proof that passes a cubic transfer to the limit must supply compactness,
-- compensated structure, or an explicit product-convergence theorem; linear
-- coefficient convergence alone is insufficient.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

data Point4 : Set where
  point0 point1 point2 point3 : Point4

Signal4 : Set
Signal4 = Point4 → ℚ

sum4 : Signal4 → ℚ
sum4 signal =
  signal point0
  + signal point1
  + signal point2
  + signal point3

oneFourth : ℚ
oneFourth = Int.+ 1 / 4

mean4 : Signal4 → ℚ
mean4 signal = oneFourth * sum4 signal

multiplySignal : Signal4 → Signal4 → Signal4
multiplySignal left right point =
  left point * right point

tripleSignal : Signal4 → Signal4 → Signal4 → Signal4
tripleSignal first second third point =
  first point * second point * third point

minusOne : ℚ
minusOne = - 1ℚ

alternatingMode : Signal4
alternatingMode point0 = 1ℚ
alternatingMode point1 = minusOne
alternatingMode point2 = 1ℚ
alternatingMode point3 = minusOne

constantOne : Signal4
constantOne _ = 1ℚ

alternatingMeanZero :
  mean4 alternatingMode ≡ 0ℚ
alternatingMeanZero = solve []

secondAlternatingMeanZero :
  mean4 alternatingMode ≡ 0ℚ
secondAlternatingMeanZero = alternatingMeanZero

alternatingSquareIsConstant :
  (point : Point4) →
  multiplySignal alternatingMode alternatingMode point
  ≡ constantOne point
alternatingSquareIsConstant point0 = solve []
alternatingSquareIsConstant point1 = solve []
alternatingSquareIsConstant point2 = solve []
alternatingSquareIsConstant point3 = solve []

alternatingSquareMeanOne :
  mean4 (multiplySignal alternatingMode alternatingMode)
  ≡ 1ℚ
alternatingSquareMeanOne = solve []

cubicTransferMeanOne :
  mean4
    (tripleSignal alternatingMode alternatingMode constantOne)
  ≡ 1ℚ
cubicTransferMeanOne = solve []

linearCancellationDoesNotForceCubicCancellation :
  mean4 alternatingMode ≡ 0ℚ
  ×
  mean4 alternatingMode ≡ 0ℚ
  ×
  mean4
    (tripleSignal alternatingMode alternatingMode constantOne)
  ≡ 1ℚ
linearCancellationDoesNotForceCubicCancellation =
  alternatingMeanZero ,
  secondAlternatingMeanZero ,
  cubicTransferMeanOne
