module DASHI.Physics.Closure.NSTriadKNCherevanFiniteOrthogonalityAuditExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Source under audit:
-- Author: Pylyp Cherevan.
-- Title: "Log-free estimate for the resonant paraproduct in the 3D
-- Navier--Stokes equations".
-- arXiv DOI: 10.48550/arXiv.2510.06246.
--
-- Littlewood--Paley reference:
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Correct the source's exact identity
--
--   ||sum_N R_N||^2 = sum_N ||R_N||^2.
--
-- Smooth neighbouring dyadic projectors generally overlap.  The exact
-- polarization identity retains the cross term 2<x,y>; equality with the
-- separated sum requires that cross term to vanish.  Littlewood--Paley theory
-- gives finite-overlap equivalence/inequalities, not exact Pythagoras across
-- every neighbouring dyad.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _*_; _<_)
open import Data.Rational.Properties as ℚₚ using (_<?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary.Decidable.Core using (toWitness)

square : ℚ → ℚ
square value = value * value

combinedSquaredMass : ℚ → ℚ → ℚ
combinedSquaredMass left right = square (left + right)

separatedSquaredMass : ℚ → ℚ → ℚ
separatedSquaredMass left right = square left + square right

crossTerm : ℚ → ℚ → ℚ
crossTerm left right = (Int.+ 2 / 1) * left * right

polarizationIdentity :
  (left right : ℚ) →
  combinedSquaredMass left right
  ≡ separatedSquaredMass left right + crossTerm left right
polarizationIdentity left right = solve (left ∷ right ∷ [])

overlapLeft overlapRight : ℚ
overlapLeft = Int.+ 1 / 1
overlapRight = Int.+ 1 / 1

overlapCombinedIsFour :
  combinedSquaredMass overlapLeft overlapRight ≡ Int.+ 4 / 1
overlapCombinedIsFour = solve []

overlapSeparatedIsTwo :
  separatedSquaredMass overlapLeft overlapRight ≡ Int.+ 2 / 1
overlapSeparatedIsTwo = solve []

exactPythagorasFailsForOverlap :
  separatedSquaredMass overlapLeft overlapRight
  < combinedSquaredMass overlapLeft overlapRight
exactPythagorasFailsForOverlap =
  toWitness
    {a? = separatedSquaredMass overlapLeft overlapRight
       ℚₚ.<? combinedSquaredMass overlapLeft overlapRight}
    _
