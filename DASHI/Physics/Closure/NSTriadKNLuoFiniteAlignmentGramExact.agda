module DASHI.Physics.Closure.NSTriadKNLuoFiniteAlignmentGramExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: B. Galanti; J. D. Gibbon; M. Heritage.
-- Title: "Vorticity Alignment Results for the Three-Dimensional Euler and
-- Navier--Stokes Equations".
-- Nonlinearity 10 (1997), 1675--1695.
-- DOI: 10.1088/0951-7715/10/6/013.
--
-- Author: Evan Miller.
-- Title: "On the Interaction of Strain and Vorticity for Solutions of the
-- Navier--Stokes Equation".
-- arXiv:2407.02691.
-- DOI: none assigned in the cited preprint version.
--
-- PURPOSE
-- Give the exact rational three-dimensional misalignment identity
--
--   ||a||^2 ||b||^2 - <a,b>^2 = ||a cross b||^2 >= 0.
--
-- This is the finite algebra behind the observable measuring failure of
-- vorticity and strain to be parallel.  It records neither a statistical
-- alignment tendency nor a continuum regularity conclusion.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _-_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

cross : V.Vector3 → V.Vector3 → V.Vector3
cross (V.v3 ax ay az) (V.v3 bx by bz) =
  V.v3
    (ay * bz - az * by)
    (az * bx - ax * bz)
    (ax * by - ay * bx)

misalignment : V.Vector3 → V.Vector3 → ℚ
misalignment a b =
  V.normSquared a * V.normSquared b - L2.square (V.dot a b)

lagrangeIdentity :
  (a b : V.Vector3) →
  misalignment a b ≡ V.normSquared (cross a b)
lagrangeIdentity (V.v3 ax ay az) (V.v3 bx by bz) =
  solve (ax ∷ ay ∷ az ∷ bx ∷ by ∷ bz ∷ [])

misalignmentNonnegative :
  (a b : V.Vector3) →
  0ℚ ≤ misalignment a b
misalignmentNonnegative a b =
  subst
    (λ value → 0ℚ ≤ value)
    (sym (lagrangeIdentity a b))
    (V.normSquaredNonnegative (cross a b))

crossWithScaledParallelZero :
  (a : V.Vector3) →
  (scale : ℚ) →
  cross a (V.scale scale a) ≡ V.v3 0ℚ 0ℚ 0ℚ
crossWithScaledParallelZero (V.v3 ax ay az) scale =
  V.vectorExt
    (solve (ax ∷ ay ∷ az ∷ scale ∷ []))
    (solve (ax ∷ ay ∷ az ∷ scale ∷ []))
    (solve (ax ∷ ay ∷ az ∷ scale ∷ []))

parallelMisalignmentZero :
  (a : V.Vector3) →
  (scale : ℚ) →
  misalignment a (V.scale scale a) ≡ 0ℚ
parallelMisalignmentZero (V.v3 ax ay az) scale =
  solve (ax ∷ ay ∷ az ∷ scale ∷ [])
