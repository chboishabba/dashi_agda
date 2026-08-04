module DASHI.Physics.Closure.NSTriadKNLuoOfficialPerModeShellMeaningExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Replace the former opaque statement that equation-(4.2) uses the official
-- Littlewood--Paley shells by a typed semantic package.  The package owns the
-- official shell energy, dissipation and time derivative and identifies all
-- three with the per-mode finite physical input at each shell.
--
-- The definitions of the official quantities remain physical analytic data;
-- the shell-index and quantity agreements can no longer be hidden in an
-- unstructured proposition token.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNLuoPerModeFiniteAssemblyAdapterExact as PerMode

record OfficialPerModeShellMeaning
    (inputs : PerMode.LuoPerModeFinitePhysicalInputs) : Set₁ where
  field
    officialShellL2Squared : Nat → ℚ
    officialShellDissipation : Nat → ℚ
    officialTimeDerivativeShellL2Squared : Nat → ℚ

    OfficialShellProjectorMeaning : Set
    officialShellProjectorMeaning : OfficialShellProjectorMeaning

    OfficialViscousMultiplierMeaning : Set
    officialViscousMultiplierMeaning : OfficialViscousMultiplierMeaning

    OfficialTimeDerivativeMeaning : Set
    officialTimeDerivativeMeaning : OfficialTimeDerivativeMeaning

    shellL2SquaredAgreement :
      (shell : Nat) →
      PerMode.shellL2Squared inputs shell
      ≡ officialShellL2Squared shell

    shellDissipationAgreement :
      (shell : Nat) →
      PerMode.shellDissipation inputs shell
      ≡ officialShellDissipation shell

    shellTimeDerivativeAgreement :
      (shell : Nat) →
      PerMode.timeDerivativeShellL2Squared inputs shell
      ≡ officialTimeDerivativeShellL2Squared shell

open OfficialPerModeShellMeaning public

record OfficialPerModeShellCoherence
    (inputs : PerMode.LuoPerModeFinitePhysicalInputs)
    (meaning : OfficialPerModeShellMeaning inputs) : Set where
  constructor coherence
  field
    energyCoherence :
      (shell : Nat) →
      PerMode.shellL2Squared inputs shell
      ≡ officialShellL2Squared meaning shell

    dissipationCoherence :
      (shell : Nat) →
      PerMode.shellDissipation inputs shell
      ≡ officialShellDissipation meaning shell

    derivativeCoherence :
      (shell : Nat) →
      PerMode.timeDerivativeShellL2Squared inputs shell
      ≡ officialTimeDerivativeShellL2Squared meaning shell

open OfficialPerModeShellCoherence public

officialPerModeShellCoherence :
  (inputs : PerMode.LuoPerModeFinitePhysicalInputs) →
  (meaning : OfficialPerModeShellMeaning inputs) →
  OfficialPerModeShellCoherence inputs meaning
officialPerModeShellCoherence inputs meaning =
  coherence
    (shellL2SquaredAgreement meaning)
    (shellDissipationAgreement meaning)
    (shellTimeDerivativeAgreement meaning)

officialPerModeShellMeaningTyped : Bool
officialPerModeShellMeaningTyped = true

threePerModeQuantityAgreementsSeparated : Bool
threePerModeQuantityAgreementsSeparated = true

officialPerModeShellMeaningTypedIsTrue :
  officialPerModeShellMeaningTyped ≡ true
officialPerModeShellMeaningTypedIsTrue = refl

threePerModeQuantityAgreementsSeparatedIsTrue :
  threePerModeQuantityAgreementsSeparated ≡ true
threePerModeQuantityAgreementsSeparatedIsTrue = refl
