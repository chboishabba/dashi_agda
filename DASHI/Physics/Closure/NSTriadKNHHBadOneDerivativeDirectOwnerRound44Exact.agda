module DASHI.Physics.Closure.NSTriadKNHHBadOneDerivativeDirectOwnerRound44Exact where

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
-- Compose the two Round-44 HH-bad reductions:
--
--   (1) a literal density plus the sole analytic scale-free coefficient bound
--       C_q <= eta/2 constructs the mature inverse-shell Round-39 certificate;
--
--   (2) the bad-mask viscous charge is automatically a subcharge of the same
--       unmasked finite shell charge.
--
-- Thus the direct HH-bad owner no longer asks separately for a factorization,
-- an inverse-shell certificate, or a bad-set dissipation allocation.  Its
-- remaining physical inputs are exactly:
--
--   * literal restricted-gain density cells;
--   * the scale-free coefficient bound;
--   * ordinary unmasked shell charge <= physical dissipation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_)

import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedGainDensityRound39Exact as Gain
import DASHI.Physics.Closure.NSTriadKNHHBadOneDerivativeFactorizationRound44Exact as Factor
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedChargeSubchargeRound44Exact as Subcharge

record PhysicalHHBadOneDerivativeOwnerInput
    (environment : Owner.TaxEnvironment)
    (effectiveViscosity eta : ℚ)
    (shell : Nat) : Set where
  field
    etaNonnegative : 0ℚ ≤ eta
    viscosityNonnegative : 0ℚ ≤ effectiveViscosity

    oneDerivativeDensity :
      Factor.PhysicalHHBadOneDerivativeDensityInput
        effectiveViscosity eta shell

    unmaskedChargeBelowPhysicalDissipation :
      Subcharge.sumCellUnmaskedViscousCharge
        effectiveViscosity shell
        (Gain.cells
          (Factor.asRound39InverseShellCertificate oneDerivativeDensity))
      ≤ Owner.dissipation environment

open PhysicalHHBadOneDerivativeOwnerInput public

asFullChargeDominationInput :
  ∀ {environment effectiveViscosity eta shell} →
  PhysicalHHBadOneDerivativeOwnerInput
    environment effectiveViscosity eta shell →
  Subcharge.HHBadFullChargeDominationInput
    environment effectiveViscosity eta shell
asFullChargeDominationInput input = record
  { etaNonnegative = etaNonnegative input
  ; viscosityNonnegative = viscosityNonnegative input
  ; densityCertificate =
      Factor.asRound39InverseShellCertificate (oneDerivativeDensity input)
  ; inverseShellTargetMeaning = refl
  ; unmaskedChargeBelowPhysicalDissipation =
      unmaskedChargeBelowPhysicalDissipation input
  }

physicalHHBadOwnerEstimate :
  ∀ {environment effectiveViscosity eta shell} →
  PhysicalHHBadOneDerivativeOwnerInput
    environment effectiveViscosity eta shell →
  Owner.AdmissibleOwnerEstimate environment
physicalHHBadOwnerEstimate input =
  Subcharge.physicalHHBadOwnerEstimateFromUnmaskedCharge
    (asFullChargeDominationInput input)

physicalHHBadOwnerIdentity :
  ∀ {environment effectiveViscosity eta shell}
    (input : PhysicalHHBadOneDerivativeOwnerInput
      environment effectiveViscosity eta shell) →
  Owner.owner (physicalHHBadOwnerEstimate input) ≡ Tax.HH-bad
physicalHHBadOwnerIdentity input = refl

physicalHHBadOwnerEtaExact :
  ∀ {environment effectiveViscosity eta shell}
    (input : PhysicalHHBadOneDerivativeOwnerInput
      environment effectiveViscosity eta shell) →
  Owner.eta (physicalHHBadOwnerEstimate input) ≡ eta
physicalHHBadOwnerEtaExact input = refl

hhBadOneDerivativeDirectOwnerCompositionClosed : Bool
hhBadOneDerivativeDirectOwnerCompositionClosed = true

hhBadOneDerivativeDirectOwnerCompositionClosedIsTrue :
  hhBadOneDerivativeDirectOwnerCompositionClosed ≡ true
hhBadOneDerivativeDirectOwnerCompositionClosedIsTrue = refl
