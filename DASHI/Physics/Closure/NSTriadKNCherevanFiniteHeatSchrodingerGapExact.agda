module DASHI.Physics.Closure.NSTriadKNCherevanFiniteHeatSchrodingerGapExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Source under audit:
-- Author: Pylyp Cherevan.
-- Title: "A log-free estimate for the diagonal paraproduct high x high to
-- low in the 3D Navier--Stokes equation".
-- arXiv:2510.07848v1.
-- arXiv DOI: 10.48550/arXiv.2510.07848.
--
-- Dispersive reference:
-- Authors: Markus Keel; Terence Tao.
-- Title: "Endpoint Strichartz Estimates".
-- DOI: 10.2307/121095.
--
-- PURPOSE
-- Give an exact finite obstruction to treating a heat block as a unitary
-- Schrodinger block without a quantitative error budget.  In the repository's
-- dyadic heat model, one resolved parabolic time unit damps the L2 amplitude
-- by 1/2.  A unitary flow preserves amplitude 1.  Their norm gap is therefore
-- exactly 1/2.
--
-- By the reverse triangle inequality, any operator comparison transferring a
-- unitary estimate to this heat block must pay at least this norm gap on the
-- witness.  The theorem below proves the arithmetic content; it does not
-- assume a continuum comparison theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _-_; _<_)
open import Data.Rational.Properties as ℚₚ using (_<?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary.Decidable.Core using (toWitness)

heatOneStepNorm schrodingerOneStepNorm : ℚ
heatOneStepNorm = Int.+ 1 / 2
schrodingerOneStepNorm = Int.+ 1 / 1

heatSchrodingerNormGap : ℚ
heatSchrodingerNormGap =
  schrodingerOneStepNorm - heatOneStepNorm

heatSchrodingerNormGapIsHalf :
  heatSchrodingerNormGap ≡ Int.+ 1 / 2
heatSchrodingerNormGapIsHalf = solve []

oneQuarter : ℚ
oneQuarter = Int.+ 1 / 4

quarterErrorCannotCoverTheGap :
  oneQuarter < heatSchrodingerNormGap
quarterErrorCannotCoverTheGap =
  toWitness {a? = oneQuarter ℚₚ.<? heatSchrodingerNormGap} _
