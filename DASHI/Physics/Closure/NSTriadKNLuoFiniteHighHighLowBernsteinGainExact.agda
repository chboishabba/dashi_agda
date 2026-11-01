module DASHI.Physics.Closure.NSTriadKNLuoFiniteHighHighLowBernsteinGainExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Record the genuine elementary high--high to low gain obtained before any
-- phase geometry.  The standard route is
--
--   ||P_q div(f_p tensor g_p)||_{H^-1}
--     <= ||P_q(f_p tensor g_p)||_2
--     <= lambda_q^(3/2) ||f_p tensor g_p||_1
--     <= lambda_q^(3/2) ||f_p||_2 ||g_p||_2.
--
-- Measuring the two high inputs in H^(1/2) and H^1 contributes
-- lambda_p^(3/2), hence the dimensionless gap coefficient is
--
--   (lambda_q/lambda_p)^(3/2) = 2^(-3 gap/2).
--
-- To avoid adjoining square roots to the rational carrier, this module proves
-- the exact squared calibration
--
--   2^(-3 gap) * (2^gap)^3 = 1
--
-- and the uniform finite l2 coefficient sum
--
--   sum_{gap=0}^N 2^(-3 gap) <= 8/7.
--
-- The Fourier Bernstein/Young estimate displayed above remains a continuum
-- producer; the frequency arithmetic and summability are completely closed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _*_; _-_; _≤_; _<_)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_; _<?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality as Eq using (subst)
open Eq.≡-Reasoning
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNLuoFiniteEnergyCriticalScalingGapExact as Scale

oneEighth eightSevenths : ℚ
oneEighth = Int.+ 1 / 8
eightSevenths = Int.+ 8 / 7

squaredBernsteinGapGain : Nat → ℚ
squaredBernsteinGapGain = Geo.pow oneEighth

cubicInputGapScale : Nat → ℚ
cubicInputGapScale gap =
  Scale.dyadicScale gap
  * Scale.dyadicScale gap
  * Scale.dyadicScale gap

squaredBernsteinGapCalibration :
  (gap : Nat) →
  squaredBernsteinGapGain gap * cubicInputGapScale gap ≡ 1ℚ
squaredBernsteinGapCalibration zero = refl
squaredBernsteinGapCalibration (suc gap) =
  begin
    squaredBernsteinGapGain (suc gap)
      * cubicInputGapScale (suc gap)
  ≡⟨ solve
       ( oneEighth
       ∷ Scale.two
       ∷ squaredBernsteinGapGain gap
       ∷ Scale.dyadicScale gap
       ∷ []) ⟩
    squaredBernsteinGapGain gap * cubicInputGapScale gap
  ≡⟨ squaredBernsteinGapCalibration gap ⟩
    1ℚ
  ∎

oneEighthNonnegative : 0ℚ ≤ oneEighth
oneEighthNonnegative = toWitness {a? = 0ℚ ≤? oneEighth} _

oneMinusOneEighthPositive : 0ℚ < 1ℚ - oneEighth
oneMinusOneEighthPositive =
  toWitness {a? = 0ℚ <? 1ℚ - oneEighth} _

eightSeventhsIdentity :
  (1ℚ - oneEighth) * eightSevenths ≡ 1ℚ
eightSeventhsIdentity = solve []

squaredBernsteinGainPrefix : Nat → ℚ
squaredBernsteinGainPrefix cutoff =
  Geo.partialSum oneEighth cutoff

squaredBernsteinGainPrefixBound :
  (cutoff : Nat) →
  squaredBernsteinGainPrefix cutoff ≤ eightSevenths
squaredBernsteinGainPrefixBound cutoff =
  Geo.geometricPartialSumBound
    oneEighth eightSevenths cutoff
    oneEighthNonnegative
    oneMinusOneEighthPositive
    eightSeventhsIdentity
