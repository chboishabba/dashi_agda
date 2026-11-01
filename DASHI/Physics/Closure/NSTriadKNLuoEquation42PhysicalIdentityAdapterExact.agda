module DASHI.Physics.Closure.NSTriadKNLuoEquation42PhysicalIdentityAdapterExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Split the remaining physical equation-(4.2) obligation into two independent
-- theorems:
--
--   1. the shell-energy inequality against the literal nonlinear Fourier RHS;
--   2. the exact identification of that RHS with the already-assembled finite
--      J1/J2 interaction fold.
--
-- Their composition supplies the existing per-mode finite physical input
-- without allowing an unrelated total-fold estimate to be postulated.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoEquation42FiniteRangeAssemblyExact as Assembly
import DASHI.Physics.Closure.NSTriadKNLuoPerModeFiniteAssemblyAdapterExact as Adapter

record LuoEquation42PhysicalIdentityInputs : Set₁ where
  field
    finiteRangeData : Assembly.Equation42FiniteRangeData

    shellL2Squared : Nat → ℚ
    shellDissipation : Nat → ℚ
    timeDerivativeShellL2Squared : Nat → ℚ

    physicalNonlinearRightHandSide : Nat → ℚ

    shellEnergyInequalityAgainstPhysicalRHS :
      (shell : Nat) →
      timeDerivativeShellL2Squared shell
        + shellDissipation shell
      ≤ physicalNonlinearRightHandSide shell

    physicalRHSMatchesTotalInteractionFold :
      (shell : Nat) →
      physicalNonlinearRightHandSide shell
      ≡ Assembly.totalInteractionSum finiteRangeData shell

open LuoEquation42PhysicalIdentityInputs public

equation42FinitePhysicalInputs :
  LuoEquation42PhysicalIdentityInputs →
  Adapter.LuoPerModeFinitePhysicalInputs
equation42FinitePhysicalInputs inputs = record
  { finiteRangeData = finiteRangeData inputs
  ; shellL2Squared = shellL2Squared inputs
  ; shellDissipation = shellDissipation inputs
  ; timeDerivativeShellL2Squared =
      timeDerivativeShellL2Squared inputs
  ; equation42AgainstTotalFold = λ shell →
      subst
        (λ upper →
          timeDerivativeShellL2Squared inputs shell
            + shellDissipation inputs shell
          ≤ upper)
        (physicalRHSMatchesTotalInteractionFold inputs shell)
        (shellEnergyInequalityAgainstPhysicalRHS inputs shell)
  }

equation42PhysicalInequalitySeparatedFromFoldIdentification : Bool
equation42PhysicalInequalitySeparatedFromFoldIdentification = true

equation42IdentityAdapterClosed : Bool
equation42IdentityAdapterClosed = true

equation42PhysicalInequalitySeparatedFromFoldIdentificationIsTrue :
  equation42PhysicalInequalitySeparatedFromFoldIdentification ≡ true
equation42PhysicalInequalitySeparatedFromFoldIdentificationIsTrue = refl

equation42IdentityAdapterClosedIsTrue :
  equation42IdentityAdapterClosed ≡ true
equation42IdentityAdapterClosedIsTrue = refl
