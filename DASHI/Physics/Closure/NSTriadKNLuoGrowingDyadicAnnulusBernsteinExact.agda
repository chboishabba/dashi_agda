module DASHI.Physics.Closure.NSTriadKNLuoGrowingDyadicAnnulusBernsteinExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Loukas Grafakos.
-- Title: "Classical Fourier Analysis".
-- DOI: 10.1007/978-1-4939-1194-3.
--
-- PURPOSE
-- Specialize the growing-cube coefficient estimate to the explicit annulus
--
--   2^(q-1) <= |k|_infinity < 2^(q+1)
--
-- intersected with an arbitrary Galerkin cutoff.  The output theorem is
--
--   sum_(k in S_(q,N)) |Fhat(k)|^2
--     <= 125 * 8^q * ||F||_1^2.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_)

import DASHI.Physics.Closure.NSTriadKNLuoGrowingFiniteCubeSupportExact as Growing
import DASHI.Physics.Closure.NSTriadKNLuoGrowingDyadicAnnulusExact as Annulus
import DASHI.Physics.Closure.NSTriadKNLuoGrowingCubeBernsteinExact as Bernstein
import DASHI.Physics.Closure.NSTriadKNLuoFiniteFourierCoefficientL1Exact as Fourier
import DASHI.Physics.Closure.NSTriadKNLuoIntegerCubeSupportCapacityExact as Capacity

record AnnularGalerkinBernsteinData (shell : Nat) : Set₁ where
  constructor annular-galerkin-bernstein-data
  field
    galerkinPredicate : Growing.ModeAt shell → Bool
    commonInputL1Squared : ℚ
    commonInputL1SquaredNonnegative : 0ℚ ≤ commonInputL1Squared
    coefficientData :
      Growing.ModeAt shell → Fourier.FiniteFourierCoefficientData
    commonInputMeaning :
      (mode : Growing.ModeAt shell) →
      Fourier.inputL1Squared (coefficientData mode)
      ≡ commonInputL1Squared

open AnnularGalerkinBernsteinData public

asGrowingBernsteinData :
  ∀ {shell : Nat} →
  AnnularGalerkinBernsteinData shell →
  Bernstein.GrowingCubeBernsteinData shell
asGrowingBernsteinData {shell} dataSet =
  Bernstein.growing-cube-bernstein-data
    (Annulus.annulusWithGalerkin shell (galerkinPredicate dataSet))
    (commonInputL1Squared dataSet)
    (commonInputL1SquaredNonnegative dataSet)
    (coefficientData dataSet)
    (commonInputMeaning dataSet)

annularGalerkinOutputL2Squared :
  (shell : Nat) →
  AnnularGalerkinBernsteinData shell → ℚ
annularGalerkinOutputL2Squared shell dataSet =
  Bernstein.outputL2Squared
    shell
    (asGrowingBernsteinData dataSet)

annularGalerkinBernsteinSquare :
  (shell : Nat) →
  (dataSet : AnnularGalerkinBernsteinData shell) →
  annularGalerkinOutputL2Squared shell dataSet
  ≤ (Capacity.oneTwentyFive * Capacity.eightPower shell)
    * commonInputL1Squared dataSet
annularGalerkinBernsteinSquare shell dataSet =
  Bernstein.growingCubeBernsteinSquare
    shell
    (asGrowingBernsteinData dataSet)
