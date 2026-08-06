module DASHI.Physics.Closure.NSTriadKNLuoSmoothLPMomentScalingExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- Communications in Mathematical Physics 165 (1994), 207--209.
-- DOI: 10.1007/BF02099744.
--
-- PURPOSE
-- Isolate and close the exact dilation algebra required to identify a smooth
-- Littlewood--Paley kernel with the centered second-moment mechanism.  For
--
--   K_q(x) = lambda_q^3 K(lambda_q x),
--
-- a change of variables gives mass invariant, first moment multiplied by
-- lambda_q^{-1}, and second moment multiplied by lambda_q^{-2}.  This module
-- proves those dyadic scaling consequences over exact rationals and
-- instantiates the normalized seed moments (0,0,1).
--
-- The remaining continuum producer is the analytic construction of a smooth
-- band-pass K on T^3/R^3 and the Bochner/Lebesgue change-of-variables theorem
-- identifying its actual integrals with the seed moments used here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteNearWindowHalfKernelExact as Near
import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

record LPMomentSeed : Set where
  constructor lp-moment-seed
  field
    mass : ℚ
    firstMoment : ℚ
    secondMoment : ℚ

open LPMomentSeed public

scaledMass : LPMomentSeed → Nat → ℚ
scaledMass seed shell = mass seed

scaledFirstMoment : LPMomentSeed → Nat → ℚ
scaledFirstMoment seed shell =
  Near.windowRoot shell * firstMoment seed

scaledSecondMoment : LPMomentSeed → Nat → ℚ
scaledSecondMoment seed shell =
  L2.square (Near.windowRoot shell) * secondMoment seed

normalizedBandpassSeed : LPMomentSeed
normalizedBandpassSeed = lp-moment-seed 0ℚ 0ℚ 1ℚ

normalizedMassZero :
  (shell : Nat) →
  scaledMass normalizedBandpassSeed shell ≡ 0ℚ
normalizedMassZero shell = refl

normalizedFirstMomentZero :
  (shell : Nat) →
  scaledFirstMoment normalizedBandpassSeed shell ≡ 0ℚ
normalizedFirstMomentZero shell =
  solve (Near.windowRoot shell ∷ [])

normalizedSecondMomentMeaning :
  (shell : Nat) →
  scaledSecondMoment normalizedBandpassSeed shell
  ≡ Near.windowLength shell
normalizedSecondMomentMeaning shell =
  solve (Near.windowRoot shell ∷ [])

scaledSecondMomentQuarters :
  (seed : LPMomentSeed) →
  (shell : Nat) →
  scaledSecondMoment seed (suc shell)
  ≡ Geo.quarter * scaledSecondMoment seed shell
scaledSecondMomentQuarters seed shell =
  solve
    ( Near.windowRoot shell
    ∷ secondMoment seed
    ∷ [])

normalizedSecondMomentQuarters :
  (shell : Nat) →
  scaledSecondMoment normalizedBandpassSeed (suc shell)
  ≡ Geo.quarter
      * scaledSecondMoment normalizedBandpassSeed shell
normalizedSecondMomentQuarters =
  scaledSecondMomentQuarters normalizedBandpassSeed
