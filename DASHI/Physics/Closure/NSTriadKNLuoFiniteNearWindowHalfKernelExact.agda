module DASHI.Physics.Closure.NSTriadKNLuoFiniteNearWindowHalfKernelExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Darko Mitrović.
-- Title: "A High-Frequency Tail Condition and a Diagnostic Iteration for
-- the Navier--Stokes Equations".
-- arXiv:2411.02568.
-- DOI: none assigned in the cited preprint version.
--
-- PURPOSE
-- Record the exact algebraic calibration of the terminal singular-kernel
-- factor
--
--   integral_0^delta tau^(-1/2) d tau = 2 sqrt(delta).
--
-- On the rational dyadic lane the window is represented by a root r,
-- delta=r^2, and the half-kernel mass is 2r.  The module proves the square-safe
-- identity mass^2=4 delta and the exact halving/quartering recursion.  The
-- analytic identification with the continuum integral remains explicit and
-- is not manufactured here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; _/_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

half two four : ℚ
half = Int.+ 1 / 2
two = Int.+ 2 / 1
four = Int.+ 4 / 1

windowRoot : Nat → ℚ
windowRoot = Geo.pow half

windowLength : Nat → ℚ
windowLength exponent = L2.square (windowRoot exponent)

halfKernelMass : Nat → ℚ
halfKernelMass exponent = two * windowRoot exponent

halfKernelSquareCalibration :
  (exponent : Nat) →
  L2.square (halfKernelMass exponent)
  ≡ four * windowLength exponent
halfKernelSquareCalibration exponent =
  solve (windowRoot exponent ∷ [])

windowRootHalves :
  (exponent : Nat) →
  windowRoot (suc exponent) ≡ half * windowRoot exponent
windowRootHalves exponent = refl

windowLengthQuarters :
  (exponent : Nat) →
  windowLength (suc exponent)
  ≡ Geo.quarter * windowLength exponent
windowLengthQuarters exponent =
  solve (windowRoot exponent ∷ [])

halfKernelMassHalves :
  (exponent : Nat) →
  halfKernelMass (suc exponent)
  ≡ half * halfKernelMass exponent
halfKernelMassHalves exponent =
  solve (windowRoot exponent ∷ [])
