module DASHI.Physics.Closure.NSTriadKNShellEnergyMinModeLowerBoundNoGoRound97Exact where

------------------------------------------------------------------------
-- SOURCES / CALIBRATION
--
-- Author: Rod Higgins.
-- Title: "Global Regularity of 3D Navier-Stokes: An Energy Argument".
-- Year: 2026 preprint supplied for Round97.
-- DOI: none identified in the supplied manuscript.
--
-- Authors: Zhen Lei; Xiao Ren.
-- Title: "Quantitative partial regularity of the Navier-Stokes equations
-- and applications".
-- arXiv:2210.01783 (2022); later publication metadata is deliberately not
-- asserted here because this module uses only the supplied manuscript.
-- DOI: not used here.
--
-- ROUND97 / FAIL-CLOSED CALIBRATION
--
-- The Higgins local-transfer argument uses, for a shell with n_j active
-- modes and total shell energy E_j, a lower bound of the form
--
--   min_k |u_k| >= c sqrt(E_j / n_j).
--
-- Such a lower bound does not follow from shell energy or mode count alone.
-- The exact two-mode countermodel below has total squared amplitude 1,
-- while one modal amplitude is exactly zero.  Thus even the c = 1, n = 2
-- instance
--
--   min |u_k|^2 >= E / 2
--
-- is false.  More generally one coefficient may be arbitrarily small while
-- another carries the fixed shell energy.  Consequently Round96/97 must use
-- finite Cauchy/multiplicity bounds and packet-boundary cancellation, never a
-- minimum-mode denominator or an unproved shell-equipartition hypothesis.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary.Decidable.Core using (toWitness)

square : ℚ → ℚ
square x = x * x

firstAmplitude secondAmplitude : ℚ
firstAmplitude = 0ℚ
secondAmplitude = 1ℚ

twoModeShellEnergy : ℚ
twoModeShellEnergy = square firstAmplitude + square secondAmplitude

twoModeShellEnergyIsOne : twoModeShellEnergy ≡ 1ℚ
twoModeShellEnergyIsOne = solve []

firstAmplitudeSquareIsZero : square firstAmplitude ≡ 0ℚ
firstAmplitudeSquareIsZero = refl

half : ℚ
half = 1 / 2
  where
  open import Data.Rational.Base using (_/_)
  open import Data.Integer.Base using (+_)

-- Avoid any dependence on a square-root carrier: the alleged lower bound
-- min |u_k| >= sqrt(E/2) implies after squaring the weaker necessary claim
-- min |u_k|^2 >= E/2.  The countermodel already refutes this squared claim.
halfPositive : 0ℚ < half
halfPositive = toWitness {a? = 0ℚ ℚP.<? half} _

zeroNotAboveHalf : ¬ (half ≤ square firstAmplitude)
zeroNotAboveHalf hyp =
  ℚP.<⇒≱ halfPositive hyp

energyHalfIsHalf : half * twoModeShellEnergy ≡ half
energyHalfIsHalf rewrite twoModeShellEnergyIsOne = solve (half ∷ [])

shellEnergyDoesNotForceFirstModeLowerBound :
  ¬ (half * twoModeShellEnergy ≤ square firstAmplitude)
shellEnergyDoesNotForceFirstModeLowerBound hyp
  rewrite energyHalfIsHalf in hyp = zeroNotAboveHalf hyp

record FixedEnergySparseShellWitness : Set where
  field
    totalEnergyIsOne : twoModeShellEnergy ≡ 1ℚ
    oneModeVanishes : square firstAmplitude ≡ 0ℚ
    positiveMeanShareNotBelowVanishingMode :
      ¬ (half * twoModeShellEnergy ≤ square firstAmplitude)

fixedEnergySparseShellWitness : FixedEnergySparseShellWitness
fixedEnergySparseShellWitness = record
  { totalEnergyIsOne = twoModeShellEnergyIsOne
  ; oneModeVanishes = firstAmplitudeSquareIsZero
  ; positiveMeanShareNotBelowVanishingMode =
      shellEnergyDoesNotForceFirstModeLowerBound
  }

round97MinimumModeLowerBoundFromShellEnergyRefuted : Bool
round97MinimumModeLowerBoundFromShellEnergyRefuted = true

round97MinimumModeLowerBoundFromShellEnergyRefutedIsTrue :
  round97MinimumModeLowerBoundFromShellEnergyRefuted ≡ true
round97MinimumModeLowerBoundFromShellEnergyRefutedIsTrue = refl
