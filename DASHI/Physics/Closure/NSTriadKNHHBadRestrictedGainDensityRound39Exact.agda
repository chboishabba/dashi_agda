module DASHI.Physics.Closure.NSTriadKNHHBadRestrictedGainDensityRound39Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Round 38 made the bad viscous charge same-object by restricting shell
-- energy with the evidence mask before summation.  The next physical theorem
-- should not differentiate that Bool mask.  Instead, treat the actual bad
-- nonlinear gain as another nonnegative charge on the *same* finite samples.
--
-- This module gives the exact finite Radon--Nikodym analogue:
--
--   gain_i <= c * viscousCharge_i   for every bad-restricted sample
--
-- implies
--
--   sum gain_i <= c * sum viscousCharge_i.
--
-- Good samples contribute zero by definition.  There is no d/dt chi_bad term,
-- no crossing distribution, and no post-hoc owner allocation.  Crossing/BV
-- control remains a separate coordinate exactly as intended in Round 38.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedDissipationRound38Exact as Bad

record RawBadGainSample : Set where
  constructor raw-bad-gain-sample
  field
    energySample : Bad.BadTaggedEnergySample
    rawGain : ℚ
    rawGainNonnegative : 0ℚ ≤ rawGain

open RawBadGainSample public

maskedGain : RawBadGainSample → ℚ
maskedGain sample with Bad.isBad (energySample sample)
... | true = rawGain sample
... | false = 0ℚ

maskedGainNonnegative : ∀ sample → 0ℚ ≤ maskedGain sample
maskedGainNonnegative sample with Bad.isBad (energySample sample)
... | true = rawGainNonnegative sample
... | false = ℚP.≤-refl

maskedGainGoodSampleZero :
  ∀ sample → Bad.isBad (energySample sample) ≡ false →
  maskedGain sample ≡ 0ℚ
maskedGainGoodSampleZero sample evidence rewrite evidence = refl

maskedGainBadSampleExact :
  ∀ sample → Bad.isBad (energySample sample) ≡ true →
  maskedGain sample ≡ rawGain sample
maskedGainBadSampleExact sample evidence rewrite evidence = refl

record RestrictedGainDensityCell
    (effectiveViscosity density : ℚ)
    (shell : Nat) : Set where
  constructor restricted-gain-density-cell
  field
    sample : RawBadGainSample
    viscousChargeNonnegative :
      0ℚ ≤ Bad.maskedViscousCharge
        effectiveViscosity shell (energySample sample)
    densityBound :
      maskedGain sample
      ≤ density * Bad.maskedViscousCharge
          effectiveViscosity shell (energySample sample)

open RestrictedGainDensityCell public

sumMaskedGain : List RawBadGainSample → ℚ
sumMaskedGain [] = 0ℚ
sumMaskedGain (sample ∷ rest) = maskedGain sample + sumMaskedGain rest

sumCellGain :
  ∀ {effectiveViscosity density shell} →
  List (RestrictedGainDensityCell effectiveViscosity density shell) → ℚ
sumCellGain [] = 0ℚ
sumCellGain (cell ∷ rest) = maskedGain (sample cell) + sumCellGain rest

sumCellViscousCharge :
  ∀ {effectiveViscosity density shell} →
  List (RestrictedGainDensityCell effectiveViscosity density shell) → ℚ
sumCellViscousCharge {effectiveViscosity} {density} {shell} [] = 0ℚ
sumCellViscousCharge {effectiveViscosity} {density} {shell} (cell ∷ rest) =
  Bad.maskedViscousCharge effectiveViscosity shell (energySample (sample cell))
  + sumCellViscousCharge rest

sumCellGainNonnegative :
  ∀ {effectiveViscosity density shell}
    (cells : List (RestrictedGainDensityCell effectiveViscosity density shell)) →
  0ℚ ≤ sumCellGain cells
sumCellGainNonnegative [] = ℚP.≤-refl
sumCellGainNonnegative (cell ∷ rest) =
  ℚP.+-mono-≤
    (maskedGainNonnegative (sample cell))
    (sumCellGainNonnegative rest)

sumCellViscousChargeNonnegative :
  ∀ {effectiveViscosity density shell}
    (cells : List (RestrictedGainDensityCell effectiveViscosity density shell)) →
  0ℚ ≤ sumCellViscousCharge cells
sumCellViscousChargeNonnegative [] = ℚP.≤-refl
sumCellViscousChargeNonnegative (cell ∷ rest) =
  ℚP.+-mono-≤
    (viscousChargeNonnegative cell)
    (sumCellViscousChargeNonnegative rest)

finiteRestrictedGainDensityBound :
  ∀ {effectiveViscosity density shell}
    (densityNN : 0ℚ ≤ density)
    (cells : List (RestrictedGainDensityCell effectiveViscosity density shell)) →
  sumCellGain cells ≤ density * sumCellViscousCharge cells
finiteRestrictedGainDensityBound {density = density} densityNN [] =
  subst
    (λ upper → 0ℚ ≤ upper)
    (solve (density ∷ []))
    ℚP.≤-refl
finiteRestrictedGainDensityBound
    {effectiveViscosity} {density} {shell}
    densityNN (cell ∷ rest) =
  let
    restBound :
      sumCellGain rest ≤ density * sumCellViscousCharge rest
    restBound = finiteRestrictedGainDensityBound densityNN rest

    addBounds :
      maskedGain (sample cell) + sumCellGain rest
      ≤
      density * Bad.maskedViscousCharge
        effectiveViscosity shell (energySample (sample cell))
      + density * sumCellViscousCharge rest
    addBounds = ℚP.+-mono-≤ (densityBound cell) restBound

    factorRight :
      density * Bad.maskedViscousCharge
        effectiveViscosity shell (energySample (sample cell))
      + density * sumCellViscousCharge rest
      ≡ density *
        (Bad.maskedViscousCharge
          effectiveViscosity shell (energySample (sample cell))
        + sumCellViscousCharge rest)
    factorRight = solve
      ( density
      ∷ Bad.maskedViscousCharge
          effectiveViscosity shell (energySample (sample cell))
      ∷ sumCellViscousCharge rest
      ∷ [])
  in
  subst
    (λ upper →
      maskedGain (sample cell) + sumCellGain rest ≤ upper)
    factorRight
    addBounds

record InverseShellRestrictedGainDensity
    (effectiveViscosity : ℚ)
    (shell : Nat) : Set where
  field
    density : ℚ
    densityNonnegative : 0ℚ ≤ density
    inverseShellTarget : ℚ
    inverseShellTargetNonnegative : 0ℚ ≤ inverseShellTarget
    densityBelowInverseShellTarget : density ≤ inverseShellTarget
    cells : List (RestrictedGainDensityCell effectiveViscosity density shell)

open InverseShellRestrictedGainDensity public

restrictedGainBelowInverseShellCharge :
  ∀ effectiveViscosity shell
    (certificate : InverseShellRestrictedGainDensity effectiveViscosity shell) →
  sumCellGain (cells certificate)
  ≤ inverseShellTarget certificate
      * sumCellViscousCharge (cells certificate)
restrictedGainBelowInverseShellCharge effectiveViscosity shell certificate =
  let
    first = finiteRestrictedGainDensityBound
      (densityNonnegative certificate) (cells certificate)

    chargeNN = sumCellViscousChargeNonnegative (cells certificate)

    second :
      density certificate * sumCellViscousCharge (cells certificate)
      ≤ inverseShellTarget certificate * sumCellViscousCharge (cells certificate)
    second =
      L2.nonnegativeProductMonotone
        (densityNonnegative certificate)
        chargeNN
        (inverseShellTargetNonnegative certificate)
        chargeNN
        (densityBelowInverseShellTarget certificate)
        ℚP.≤-refl
  in
  ℚP.≤-trans first second

hhBadFiniteRestrictedGainDensityClosed : Bool
hhBadFiniteRestrictedGainDensityClosed = true

physicalHHBadGainDensityCellsConstructed : Bool
physicalHHBadGainDensityCellsConstructed = false

physicalLuoCriticalDissipationSmallnessConstructed : Bool
physicalLuoCriticalDissipationSmallnessConstructed = false

hhBadFiniteRestrictedGainDensityClosedIsTrue :
  hhBadFiniteRestrictedGainDensityClosed ≡ true
hhBadFiniteRestrictedGainDensityClosedIsTrue = refl
