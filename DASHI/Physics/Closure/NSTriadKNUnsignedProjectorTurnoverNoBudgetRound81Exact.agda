module DASHI.Physics.Closure.NSTriadKNUnsignedProjectorTurnoverNoBudgetRound81Exact where

------------------------------------------------------------------------
-- ROUND81 / UNSIGNED PROJECTOR PATH-LENGTH NO-GO
--
-- The existing bounded-turnover lane correctly distinguishes unsigned
-- spectral-projector path length from one-sided escape of a bounded potential.
-- This file gives the cheapest exact finite witness.
--
-- Let P1 and P2 be the orthogonal line projectors onto e1 and e2.  The closed
-- path
--
--     P1 -> P2 -> P1
--
-- has strictly positive squared Frobenius motion on both legs, while the
-- bounded directional potential observed by e3 is exactly zero at every point.
-- Thus unsigned projector turnover cannot itself be treated as a finite
-- endpoint budget.  It may be a local mechanism, but C5/C6 must charge a signed
-- bounded-potential escape (or another genuinely finite additive currency).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as M
import DASHI.Physics.Closure.NSTriadKNCorrectedFourierAngularStrainExact as A

p1 p2 : M.Matrix3
p1 = M.matrix3
  1ℚ 0ℚ 0ℚ
  0ℚ 0ℚ 0ℚ
  0ℚ 0ℚ 0ℚ

p2 = M.matrix3
  0ℚ 0ℚ 0ℚ
  0ℚ 1ℚ 0ℚ
  0ℚ 0ℚ 0ℚ

e3 : V.Vector3
e3 = V.v3 0ℚ 0ℚ 1ℚ

matrixDifferenceSquareEnergy : M.Matrix3 → M.Matrix3 → ℚ
matrixDifferenceSquareEnergy left right =
    (M.m11 left - M.m11 right) * (M.m11 left - M.m11 right)
  + (M.m12 left - M.m12 right) * (M.m12 left - M.m12 right)
  + (M.m13 left - M.m13 right) * (M.m13 left - M.m13 right)
  + (M.m21 left - M.m21 right) * (M.m21 left - M.m21 right)
  + (M.m22 left - M.m22 right) * (M.m22 left - M.m22 right)
  + (M.m23 left - M.m23 right) * (M.m23 left - M.m23 right)
  + (M.m31 left - M.m31 right) * (M.m31 left - M.m31 right)
  + (M.m32 left - M.m32 right) * (M.m32 left - M.m32 right)
  + (M.m33 left - M.m33 right) * (M.m33 left - M.m33 right)

forwardMotionSquare : matrixDifferenceSquareEnergy p1 p2 ≡ 1ℚ + 1ℚ
forwardMotionSquare = refl

returnMotionSquare : matrixDifferenceSquareEnergy p2 p1 ≡ 1ℚ + 1ℚ
returnMotionSquare = refl

closedLoopUnsignedMotionSquare : ℚ
closedLoopUnsignedMotionSquare =
  matrixDifferenceSquareEnergy p1 p2 + matrixDifferenceSquareEnergy p2 p1

closedLoopUnsignedMotionSquareIsFour :
  closedLoopUnsignedMotionSquare ≡ (1ℚ + 1ℚ) + (1ℚ + 1ℚ)
closedLoopUnsignedMotionSquareIsFour = refl

-- Directional bounded potential x^T P x for the fixed unit vector e3.
directionalPotential : M.Matrix3 → ℚ
directionalPotential projector =
  V.dot e3 (A.apply projector e3)

p1PotentialZero : directionalPotential p1 ≡ 0ℚ
p1PotentialZero = refl

p2PotentialZero : directionalPotential p2 ≡ 0ℚ
p2PotentialZero = refl

closedLoopNetPotentialChangeZero :
  directionalPotential p1 - directionalPotential p1 ≡ 0ℚ
closedLoopNetPotentialChangeZero = refl

round81UnsignedProjectorTurnoverIsFiniteEndpointBudget : Bool
round81UnsignedProjectorTurnoverIsFiniteEndpointBudget = false

round81SignedBoundedPotentialEscapeStillRequired : Bool
round81SignedBoundedPotentialEscapeStillRequired = true

round81UnsignedProjectorTurnoverIsFiniteEndpointBudgetIsFalse :
  round81UnsignedProjectorTurnoverIsFiniteEndpointBudget ≡ false
round81UnsignedProjectorTurnoverIsFiniteEndpointBudgetIsFalse = refl
