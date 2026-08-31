module DASHI.Physics.Closure.NSAncientIncrementStructureFluxLinearizationRound66Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Theodore von Karman; Leslie Howarth.
-- Title: "On the Statistical Theory of Isotropic Turbulence".
-- Proceedings of the Royal Society A 164 (1938), 192--215.
-- DOI: 10.1098/rspa.1938.0013.
--
-- Authors: Jean Duchon; Raoul Robert.
-- Title: "Inertial energy dissipation for weak solutions of incompressible
--         Euler and Navier-Stokes equations".
-- Nonlinearity 13 (2000), 249--255.
-- DOI: 10.1088/0951-7715/13/1/312.
--
-- Authors: Gabriel Koch; Nikolai Nadirashvili; Gregory A. Seregin;
--          Vladimir Sverak.
-- Title: "Liouville theorems for the Navier-Stokes equations and applications".
-- Acta Mathematica 203 (2009), 83--105.
-- DOI: 10.1007/s11511-009-0039-6.
--
-- ROUND66 / POSITIVE OPENING: BOUNDED ANCIENT NORMALIZATION LINEARIZES THE
-- THIRD-ORDER STRUCTURE FLUX BY THE SECOND-ORDER INCREMENT DEFECT.
--
-- The exact Karman--Howarth/Duchon--Robert increment flux is cubic in delta u.
-- Bare amplitude homogeneity therefore looks hostile.  But the KNSŠ ancient
-- normalization supplies |U| <= 1, hence |delta_h U| <= 2.  Pointwise,
--
--   0 <= x <= B  =>  x^3 <= B x^2.
--
-- This file proves that estimate and its finite-sum version exactly over Q:
--
--   sum x_i^3 <= B * sum x_i^2.
--
-- Therefore, after bounded blow-up normalization, the third-order structure
-- flux has a LINEAR envelope in the second-order structure defect.  This does
-- not control the separation-space divergence of the flux; that remains the
-- genuine C-unit PDE step.  But it is a real mechanism distinct from trying
-- to absorb an arbitrary cubic into quadratic viscous dissipation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteRationalOrderCore as Order

square : ℚ → ℚ
square x = x * x

cubic : ℚ → ℚ
cubic x = x * square x

boundedCubicByQuadratic :
  (B x : ℚ) →
  0ℚ ≤ x →
  x ≤ B →
  cubic x ≤ B * square x
boundedCubicByQuadratic B x xNN x≤B =
  let
    squareNN : 0ℚ ≤ square x
    squareNN = Order.squareNonnegative x

    instance squareNonnegative : NonNegative (square x)
        squareNonnegative = nonNegative squareNN
  in
  ℚP.*-monoʳ-≤-nonNeg (square x) x≤B

data BoundedMagnitudes (B : ℚ) : List ℚ → Set where
  bounded[] : BoundedMagnitudes B []
  bounded∷ :
    ∀ {x xs} →
    0ℚ ≤ x →
    x ≤ B →
    BoundedMagnitudes B xs →
    BoundedMagnitudes B (x ∷ xs)

sumSquares : List ℚ → ℚ
sumSquares [] = 0ℚ
sumSquares (x ∷ xs) = square x + sumSquares xs

sumCubics : List ℚ → ℚ
sumCubics [] = 0ℚ
sumCubics (x ∷ xs) = cubic x + sumCubics xs

boundedThirdOrderSumBySecondOrderSum :
  (B : ℚ) →
  (xs : List ℚ) →
  BoundedMagnitudes B xs →
  sumCubics xs ≤ B * sumSquares xs
boundedThirdOrderSumBySecondOrderSum B [] bounded[] =
  ℚP.≤-refl
boundedThirdOrderSumBySecondOrderSum B (x ∷ xs) (bounded∷ xNN x≤B tailBounded) =
  let
    head : cubic x ≤ B * square x
    head = boundedCubicByQuadratic B x xNN x≤B

    tail : sumCubics xs ≤ B * sumSquares xs
    tail = boundedThirdOrderSumBySecondOrderSum B xs tailBounded

    added : cubic x + sumCubics xs ≤ B * square x + B * sumSquares xs
    added = ℚP.+-mono-≤ head tail
  in
  subst
    (λ upper → cubic x + sumCubics xs ≤ upper)
    (solve (B ∷ square x ∷ sumSquares xs ∷ []))
    added

-- The KNSŠ normalization |U| <= 1 gives |delta_h U| <= 2.  Consumers may
-- instantiate B with the literal rational 2 once their norm/triangle bridge
-- has transported the analytic bound into this finite scalar carrier.
