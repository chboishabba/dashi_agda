module DASHI.Physics.Closure.NSTriadKNHHBadNormalizedProfileRound45Exact where

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
-- Round 44 proved that the inverse-shell factorization is algebraic.  The
-- remaining HH-bad scalar is therefore the normalized shell coefficient
--
--   C_q = 2^q g_q.
--
-- This file makes the research target literal.  A uniform physical profile
-- supplies one ceiling C_* with C_q <= C_* for every shell.  The canonical
-- owner tax is then
--
--   eta_HHb = 2 C_*.
--
-- Since (2 C_*)/2 = C_* exactly, the profile ceiling constructs every Round-44
-- one-derivative density input.  If the corresponding unmasked shell charges
-- are subcharges of physical dissipation, the existing direct owner theorem
-- yields an HH-bad owner at every shell with eta exactly 2 C_*.
--
-- Thus the unresolved analytic theorem is no longer vaguely "inverse-shell
-- decay": it is the cutoff-uniform bound on the dimensionless normalized
-- profile C_q, together with the literal positive-shell decomposition that
-- supplies the cells.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedGainDensityRound39Exact as Gain
import DASHI.Physics.Closure.NSTriadKNHHBadOneDerivativeFactorizationRound44Exact as Factor
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedChargeSubchargeRound44Exact as Subcharge
import DASHI.Physics.Closure.NSTriadKNHHBadOneDerivativeDirectOwnerRound44Exact as Direct

record UniformHHBadNormalizedProfile
    (effectiveViscosity : ℚ) : Set where
  field
    density : Nat → ℚ
    densityNonnegative : ∀ shell → 0ℚ ≤ density shell

    cells : ∀ shell →
      List (Gain.RestrictedGainDensityCell
        effectiveViscosity (density shell) shell)

    profileCeiling : ℚ
    profileCeilingNonnegative : 0ℚ ≤ profileCeiling

    normalizedCoefficientBelowCeiling : ∀ shell →
      Factor.scaleFreeDensityCoefficient (density shell) shell
      ≤ profileCeiling

open UniformHHBadNormalizedProfile public

canonicalHHBadEta :
  ∀ {effectiveViscosity} →
  UniformHHBadNormalizedProfile effectiveViscosity → ℚ
canonicalHHBadEta profile = Sharp.two * profileCeiling profile

canonicalHHBadEtaNonnegative :
  ∀ {effectiveViscosity}
    (profile : UniformHHBadNormalizedProfile effectiveViscosity) →
  0ℚ ≤ canonicalHHBadEta profile
canonicalHHBadEtaNonnegative profile =
  let
    twoNN : 0ℚ ≤ Sharp.two
    twoNN = ℚP.nonNegative⁻¹ Sharp.two
    instance
      twoNNI = nonNegative twoNN
      ceilingNNI = nonNegative (profileCeilingNonnegative profile)
      productNNI =
        ℚP.nonNeg*nonNeg⇒nonNeg Sharp.two (profileCeiling profile)
  in
  ℚP.nonNegative⁻¹ (canonicalHHBadEta profile)

ceilingEqualsCanonicalHalfEta :
  ∀ {effectiveViscosity}
    (profile : UniformHHBadNormalizedProfile effectiveViscosity) →
  profileCeiling profile
  ≡ canonicalHHBadEta profile * Sharp.half
ceilingEqualsCanonicalHalfEta profile =
  solve (profileCeiling profile ∷ [])

canonicalOneDerivativeDensityAtShell :
  ∀ {effectiveViscosity}
    (profile : UniformHHBadNormalizedProfile effectiveViscosity) →
  (shell : Nat) →
  Factor.PhysicalHHBadOneDerivativeDensityInput
    effectiveViscosity (canonicalHHBadEta profile) shell
canonicalOneDerivativeDensityAtShell profile shell = record
  { density = density profile shell
  ; densityNonnegative = densityNonnegative profile shell
  ; cells = cells profile shell
  ; physicalHHBadScaleFreeCoefficientBound =
      subst
        (λ upper →
          Factor.scaleFreeDensityCoefficient (density profile shell) shell
          ≤ upper)
        (ceilingEqualsCanonicalHalfEta profile)
        (normalizedCoefficientBelowCeiling profile shell)
  }

record PhysicalUniformHHBadOwnerProfile
    (environment : Owner.TaxEnvironment)
    (effectiveViscosity : ℚ) : Set where
  field
    normalizedProfile : UniformHHBadNormalizedProfile effectiveViscosity
    viscosityNonnegative : 0ℚ ≤ effectiveViscosity

    unmaskedChargeBelowPhysicalDissipation : ∀ shell →
      Subcharge.sumCellUnmaskedViscousCharge
        effectiveViscosity shell
        (Gain.cells
          (Factor.asRound39InverseShellCertificate
            (canonicalOneDerivativeDensityAtShell
              normalizedProfile shell)))
      ≤ Owner.dissipation environment

open PhysicalUniformHHBadOwnerProfile public

physicalHHBadOwnerInputAtShell :
  ∀ {environment effectiveViscosity}
    (profile : PhysicalUniformHHBadOwnerProfile
      environment effectiveViscosity) →
  (shell : Nat) →
  Direct.PhysicalHHBadOneDerivativeOwnerInput
    environment effectiveViscosity
    (canonicalHHBadEta (normalizedProfile profile)) shell
physicalHHBadOwnerInputAtShell profile shell = record
  { etaNonnegative =
      canonicalHHBadEtaNonnegative (normalizedProfile profile)
  ; viscosityNonnegative = viscosityNonnegative profile
  ; oneDerivativeDensity =
      canonicalOneDerivativeDensityAtShell
        (normalizedProfile profile) shell
  ; unmaskedChargeBelowPhysicalDissipation =
      unmaskedChargeBelowPhysicalDissipation profile shell
  }

physicalHHBadOwnerAtShell :
  ∀ {environment effectiveViscosity}
    (profile : PhysicalUniformHHBadOwnerProfile
      environment effectiveViscosity) →
  Nat → Owner.AdmissibleOwnerEstimate environment
physicalHHBadOwnerAtShell profile shell =
  Direct.physicalHHBadOwnerEstimate
    (physicalHHBadOwnerInputAtShell profile shell)

physicalHHBadOwnerAtShellIdentity :
  ∀ {environment effectiveViscosity}
    (profile : PhysicalUniformHHBadOwnerProfile
      environment effectiveViscosity) →
  ∀ shell →
  Owner.owner (physicalHHBadOwnerAtShell profile shell) ≡ Tax.HH-bad
physicalHHBadOwnerAtShellIdentity profile shell = refl

physicalHHBadOwnerEtaIsTwiceProfileCeiling :
  ∀ {environment effectiveViscosity}
    (profile : PhysicalUniformHHBadOwnerProfile
      environment effectiveViscosity) →
  ∀ shell →
  Owner.eta (physicalHHBadOwnerAtShell profile shell)
  ≡ Sharp.two * profileCeiling (normalizedProfile profile)
physicalHHBadOwnerEtaIsTwiceProfileCeiling profile shell = refl

hhBadReducedToUniformNormalizedProfile : Bool
hhBadReducedToUniformNormalizedProfile = true

hhBadReducedToUniformNormalizedProfileIsTrue :
  hhBadReducedToUniformNormalizedProfile ≡ true
hhBadReducedToUniformNormalizedProfileIsTrue = refl
