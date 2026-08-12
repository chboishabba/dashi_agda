module DASHI.Physics.Closure.NSTriadKNHHGoodFiniteCoefficientContinuationAuditRound46Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
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
-- Round 46 audits the claim that HH-good's annular/parabolic constant need not
-- itself be small once the owner is proved Young-soft.  At the actual
-- nine-owner absorption seam, residual viscosity depends ONLY on the eta list:
--
--   1 - sum eta_i.
--
-- Every critical coefficient, including the HH-good coefficient produced by
-- the annular/parabolic estimate, enters only the admissible remainder
--
--   sum A_i + (sum B_i) X.
--
-- Therefore no smallness of B_HHg is required by the viscosity-reserve or
-- integrated-cutoff-energy algebra itself.  A finite cutoff-uniform coefficient
-- is admissible there.  This file deliberately does NOT claim that an arbitrary
-- huge B automatically closes the later block-decay majorant: the existing
-- ReserveToBlockDecayBridge may still impose a quantitative downstream bound
-- when its explicit majorant and recursion coefficient are constructed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (1ℚ; _+_; _-_; _*_)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNNineOwnerCriticalAbsorptionRound28Exact as Nine
import DASHI.Physics.Closure.NSTriadKNNineOwnerToBlockDecayBridgeRound43Exact as Bridge

residualViscosityUsesOnlyEtaTotal :
  (balance : Nine.NineOwnerCriticalBalance) →
  Nine.remainingViscosity balance
  ≡ 1ℚ - Owner.sumEta (Owner.nineOwnerList (Nine.family balance))
residualViscosityUsesOnlyEtaTotal balance = refl

admissibleRemainderUsesCriticalCoefficientsOnlyAsRemainder :
  (balance : Nine.NineOwnerCriticalBalance) →
  Nine.admissibleRemainder balance
  ≡ Owner.sumDataRemainder estimates
    + Owner.sumCriticalCoefficient estimates
      * Owner.integralCritical (Nine.environment balance)
admissibleRemainderUsesCriticalCoefficientsOnlyAsRemainder balance = refl
  where
  estimates = Owner.nineOwnerList (Nine.family balance)

integratedCutoffEnergyUsesSameResidualViscosity :
  (balance : Nine.NineOwnerCriticalBalance) →
  Bridge.NineOwnerIntegratedCutoffEnergyInequality balance
integratedCutoffEnergyUsesSameResidualViscosity =
  Bridge.physicalNineOwnerBalanceToIntegratedCutoffEnergyInequality

hhGoodCriticalCoefficientSmallnessNotRequiredByReserveAlgebra : Bool
hhGoodCriticalCoefficientSmallnessNotRequiredByReserveAlgebra = true

hhGoodCriticalCoefficientMayStillEnterDownstreamMajorant : Bool
hhGoodCriticalCoefficientMayStillEnterDownstreamMajorant = true

hhGoodCriticalCoefficientSmallnessNotRequiredByReserveAlgebraIsTrue :
  hhGoodCriticalCoefficientSmallnessNotRequiredByReserveAlgebra ≡ true
hhGoodCriticalCoefficientSmallnessNotRequiredByReserveAlgebraIsTrue = refl

hhGoodCriticalCoefficientMayStillEnterDownstreamMajorantIsTrue :
  hhGoodCriticalCoefficientMayStillEnterDownstreamMajorant ≡ true
hhGoodCriticalCoefficientMayStillEnterDownstreamMajorantIsTrue = refl
