module DASHI.Physics.Closure.NSTriadKNCanonicalOwnerFluxCorrectionRound55Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Close the Round-54 same-object seam by choosing one canonical definition:
-- the additive physical flux correction IS the complete signed nine-owner
-- remainder produced by the localized identity.  This is not an estimate and
-- does not alter Luo's multiplicative shift coefficient.
--
-- The resulting FixedShiftRecursionPhysicalData has
--   integratedFluxCorrection q = admissibleRemainder (balances q)
-- definitionally, so SameObjectOwnerToFixedShiftCorrection is refl.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNNineOwnerCriticalAbsorptionRound28Exact as Nine
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftRecursionReductionExact as Fixed
import DASHI.Physics.Closure.NSTriadKNFixedShiftCoefficientSeparationRound53Exact as Sep

record CanonicalOwnerDrivenFixedShift
    (balances : Nat → Nine.NineOwnerCriticalBalance) : Set₁ where
  field
    cutoffEnergy cutoffDissipation : Nat → ℚ
    predecessorByFixedShift : Nat → Nat
    correctedShiftCoefficient : ℚ
    selectedMaximum : ℚ → ℚ → ℚ
    sufficientlyLarge : Nat → Set

    maximumBelowEnergyDissipationSum :
      (shell : Nat) →
      selectedMaximum (cutoffEnergy shell) (cutoffDissipation shell)
      ≤ cutoffEnergy shell + cutoffDissipation shell

    localizedIdentityEnergyInequality :
      (shell : Nat) → sufficientlyLarge shell →
      cutoffEnergy shell + cutoffDissipation shell
      ≤ correctedShiftCoefficient * cutoffDissipation (predecessorByFixedShift shell)
        + Nine.admissibleRemainder (balances shell)

open CanonicalOwnerDrivenFixedShift public

asPhysicalFixedShiftData :
  ∀ {balances} →
  CanonicalOwnerDrivenFixedShift balances →
  Fixed.FixedShiftRecursionPhysicalData
asPhysicalFixedShiftData {balances} core = record
  { cutoffEnergy = cutoffEnergy core
  ; cutoffDissipation = cutoffDissipation core
  ; predecessorByFixedShift = predecessorByFixedShift core
  ; correctedShiftCoefficient = correctedShiftCoefficient core
  ; integratedFluxCorrection = λ shell → Nine.admissibleRemainder (balances shell)
  ; selectedMaximum = selectedMaximum core
  ; sufficientlyLarge = sufficientlyLarge core
  ; maximumBelowEnergyDissipationSum = maximumBelowEnergyDissipationSum core
  ; integratedCutoffEnergyInequality = localizedIdentityEnergyInequality core
  }

canonicalOwnerToFluxSameObject :
  ∀ {balances} (core : CanonicalOwnerDrivenFixedShift balances) →
  Sep.SameObjectOwnerToFixedShiftCorrection
    balances (asPhysicalFixedShiftData core)
canonicalOwnerToFluxSameObject core = record
  { ownerRemainderIsFluxCorrection = λ shell → refl }

canonicalFluxCorrectionFormula :
  ∀ {balances} (core : CanonicalOwnerDrivenFixedShift balances) shell →
  Fixed.integratedFluxCorrection (asPhysicalFixedShiftData core) shell
  ≡ Sep.ownerAggregateDataRemainder (balances shell)
    + Sep.ownerAggregateCriticalCoefficient (balances shell)
      * Owner.integralCritical (Nine.environment (balances shell))
canonicalFluxCorrectionFormula {balances} core shell =
  Sep.ownerRemainderFormula (balances shell)

ownerFluxSameObjectNowDefinitional : Bool
ownerFluxSameObjectNowDefinitional = true

ownerFluxSameObjectNowDefinitionalIsTrue :
  ownerFluxSameObjectNowDefinitional ≡ true
ownerFluxSameObjectNowDefinitionalIsTrue = refl
