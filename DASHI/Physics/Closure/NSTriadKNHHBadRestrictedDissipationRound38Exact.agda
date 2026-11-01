module DASHI.Physics.Closure.NSTriadKNHHBadRestrictedDissipationRound38Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Round 37 showed that ordinary shell viscosity already has the correct lower
-- scaling for HH-bad coercivity; the real issue is same-object allocation.
-- This module removes that bookkeeping ambiguity on the finite trajectory by
-- defining the bad viscous charge by restriction to the evidence-indexed bad
-- samples themselves.
--
-- For a fixed shell q and viscosity nu, each sample carries shell energy E and
-- a Bool bad tag.  The restricted quantities are
--
--   E_bad = chi_bad E,
--   C_bad = chi_bad E * nu * lambda_q^2.
--
-- Therefore, after finite summation,
--
--   C_bad = (sum E_bad) * nu * lambda_q^2
--
-- exactly, with no independently supplied owner allocation.  The existing
-- Round-37 shell coercivity theorem then gives the normalized and inverse-shell
-- charging estimates for this restricted charge.  The remaining physical
-- theorem is to identify the actual trajectory bad predicate/gain with this
-- finite mask and pass the restriction to the continuum/time integral.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; trans)

import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHHBadStandardShellCoercivityRound37Exact as Standard

record BadTaggedEnergySample : Set where
  constructor bad-tagged-energy-sample
  field
    isBad : Bool
    shellEnergy : ℚ
    shellEnergyNonnegative : 0ℚ ≤ shellEnergy

open BadTaggedEnergySample public

maskedEnergy : BadTaggedEnergySample → ℚ
maskedEnergy sample with isBad sample
... | true = shellEnergy sample
... | false = 0ℚ

maskedEnergyNonnegative : ∀ sample → 0ℚ ≤ maskedEnergy sample
maskedEnergyNonnegative sample with isBad sample
... | true = shellEnergyNonnegative sample
... | false = ℚP.≤-refl

sumMaskedEnergy : List BadTaggedEnergySample → ℚ
sumMaskedEnergy [] = 0ℚ
sumMaskedEnergy (sample ∷ rest) =
  maskedEnergy sample + sumMaskedEnergy rest

sumMaskedEnergyNonnegative : ∀ samples → 0ℚ ≤ sumMaskedEnergy samples
sumMaskedEnergyNonnegative [] = ℚP.≤-refl
sumMaskedEnergyNonnegative (sample ∷ rest) =
  ℚP.+-mono-≤
    (maskedEnergyNonnegative sample)
    (sumMaskedEnergyNonnegative rest)

maskedViscousCharge : ℚ → Nat → BadTaggedEnergySample → ℚ
maskedViscousCharge effectiveViscosity shell sample =
  maskedEnergy sample * effectiveViscosity
    * (Sharp.dyadicScale shell * Sharp.dyadicScale shell)

sumMaskedViscousCharge :
  ℚ → Nat → List BadTaggedEnergySample → ℚ
sumMaskedViscousCharge effectiveViscosity shell [] = 0ℚ
sumMaskedViscousCharge effectiveViscosity shell (sample ∷ rest) =
  maskedViscousCharge effectiveViscosity shell sample
  + sumMaskedViscousCharge effectiveViscosity shell rest

sumMaskedViscousChargeFactorizes :
  ∀ effectiveViscosity shell samples →
  sumMaskedViscousCharge effectiveViscosity shell samples
  ≡
  sumMaskedEnergy samples * effectiveViscosity
    * (Sharp.dyadicScale shell * Sharp.dyadicScale shell)
sumMaskedViscousChargeFactorizes effectiveViscosity shell [] =
  solve
    ( effectiveViscosity
    ∷ Sharp.dyadicScale shell
    ∷ [])
sumMaskedViscousChargeFactorizes effectiveViscosity shell (sample ∷ rest)
  rewrite sumMaskedViscousChargeFactorizes effectiveViscosity shell rest =
  solve
    ( maskedEnergy sample
    ∷ sumMaskedEnergy rest
    ∷ effectiveViscosity
    ∷ Sharp.dyadicScale shell
    ∷ [])

restrictedFullShellCharge :
  (effectiveViscosity : ℚ) →
  (shell : Nat) →
  (samples : List BadTaggedEnergySample) →
  0ℚ ≤ effectiveViscosity →
  Standard.FullShellViscousCharge effectiveViscosity shell
restrictedFullShellCharge effectiveViscosity shell samples viscosityNN =
  Standard.full-shell-viscous-charge
    (sumMaskedEnergy samples)
    (sumMaskedEnergyNonnegative samples)
    viscosityNN

restrictedChargeMatchesStandardFullCharge :
  ∀ effectiveViscosity shell samples viscosityNN →
  sumMaskedViscousCharge effectiveViscosity shell samples
  ≡ Standard.fullViscousCharge
      (restrictedFullShellCharge
        effectiveViscosity shell samples viscosityNN)
restrictedChargeMatchesStandardFullCharge
    effectiveViscosity shell samples viscosityNN =
  sumMaskedViscousChargeFactorizes effectiveViscosity shell samples

restrictedBadViscosityDominatesNormalizedRate :
  ∀ effectiveViscosity shell samples →
  (viscosityNN : 0ℚ ≤ effectiveViscosity) →
  sumMaskedEnergy samples
    * (effectiveViscosity * Sharp.dyadicScale shell)
  ≤ sumMaskedViscousCharge effectiveViscosity shell samples
restrictedBadViscosityDominatesNormalizedRate
    effectiveViscosity shell samples viscosityNN =
  subst
    (λ charge →
      sumMaskedEnergy samples
        * (effectiveViscosity * Sharp.dyadicScale shell)
      ≤ charge)
    (symmetry
      (restrictedChargeMatchesStandardFullCharge
        effectiveViscosity shell samples viscosityNN))
    (Standard.fullShellViscosityDominatesNormalizedRate
      (restrictedFullShellCharge
        effectiveViscosity shell samples viscosityNN))
  where
  symmetry : ∀ {a b : ℚ} → a ≡ b → b ≡ a
  symmetry refl = refl

restrictedBadViscosityProducesInverseShellCharging :
  ∀ effectiveViscosity shell samples →
  (viscosityNN : 0ℚ ≤ effectiveViscosity) →
  sumMaskedEnergy samples * effectiveViscosity
  ≤ sumMaskedViscousCharge effectiveViscosity shell samples
      * Sharp.inverseDyadicScale shell
restrictedBadViscosityProducesInverseShellCharging
    effectiveViscosity shell samples viscosityNN =
  subst
    (λ charge →
      sumMaskedEnergy samples * effectiveViscosity
      ≤ charge * Sharp.inverseDyadicScale shell)
    (symmetry
      (restrictedChargeMatchesStandardFullCharge
        effectiveViscosity shell samples viscosityNN))
    (Standard.fullShellViscosityProducesInverseShellCharging
      (restrictedFullShellCharge
        effectiveViscosity shell samples viscosityNN))
  where
  symmetry : ∀ {a b : ℚ} → a ≡ b → b ≡ a
  symmetry refl = refl

hhBadRestrictedDissipationAllocationClosed : Bool
hhBadRestrictedDissipationAllocationClosed = true

physicalHHBadTrajectoryMaskIdentified : Bool
physicalHHBadTrajectoryMaskIdentified = false

physicalHHBadRestrictedGainEstimateConstructed : Bool
physicalHHBadRestrictedGainEstimateConstructed = false

hhBadRestrictedDissipationAllocationClosedIsTrue :
  hhBadRestrictedDissipationAllocationClosed ≡ true
hhBadRestrictedDissipationAllocationClosedIsTrue = refl
