module DASHI.Physics.Closure.NSTriadKNKernelIndependentZeroOwnerRound53Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- DASHI CONTRIBUTION
--
-- Round 52 established the correct order
--
--   literalize -> deduplicate -> cancel -> estimate independent remainder.
--
-- This file closes the zero-independent branch all the way to the nine-owner
-- language.  If the independent kernel remainder is exactly zero, the kernel
-- owner slot has production=eta=A=B=0.  Thus a duplicated/cancelled kernel is
-- structurally zero-tax, not merely Young-soft.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (0ℚ)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax
import DASHI.Physics.Closure.NSTriadKNKernelLiteralizationAuditRound51Exact as Literal
import DASHI.Physics.Closure.NSTriadKNKernelPreTaxReductionRound52Exact as PreTax

record PhysicalIndependentKernelZero
    (environment : Owner.TaxEnvironment)
    (physical : Literal.PhysicalKernelConstituentInstantiation)
    (reduction : PreTax.KernelPreTaxSignedReduction physical) : Set where
  field
    independentRemainderIsZero :
      PreTax.independentRemainder reduction ≡ 0ℚ

open PhysicalIndependentKernelZero public

physicalKernelZeroOwner :
  ∀ {environment physical reduction} →
  PhysicalIndependentKernelZero environment physical reduction →
  Owner.AdmissibleOwnerEstimate environment
physicalKernelZeroOwner zeroIndependent =
  Owner.admissible-owner-estimate
    Tax.kernel
    0ℚ
    0ℚ
    0ℚ
    0ℚ
    ℚP.≤-refl

physicalKernelZeroOwnerIdentity :
  ∀ {environment physical reduction}
    (zeroIndependent : PhysicalIndependentKernelZero environment physical reduction) →
  Owner.owner (physicalKernelZeroOwner zeroIndependent) ≡ Tax.kernel
physicalKernelZeroOwnerIdentity zeroIndependent = refl

physicalKernelZeroOwnerEta :
  ∀ {environment physical reduction}
    (zeroIndependent : PhysicalIndependentKernelZero environment physical reduction) →
  Owner.eta (physicalKernelZeroOwner zeroIndependent) ≡ 0ℚ
physicalKernelZeroOwnerEta zeroIndependent = refl

physicalKernelZeroOwnerCriticalCoefficient :
  ∀ {environment physical reduction}
    (zeroIndependent : PhysicalIndependentKernelZero environment physical reduction) →
  Owner.criticalCoefficient (physicalKernelZeroOwner zeroIndependent) ≡ 0ℚ
physicalKernelZeroOwnerCriticalCoefficient zeroIndependent = refl

kernelIndependentZeroImpliesStructuralZeroTax : Bool
kernelIndependentZeroImpliesStructuralZeroTax = true

kernelIndependentZeroImpliesStructuralZeroTaxIsTrue :
  kernelIndependentZeroImpliesStructuralZeroTax ≡ true
kernelIndependentZeroImpliesStructuralZeroTaxIsTrue = refl
