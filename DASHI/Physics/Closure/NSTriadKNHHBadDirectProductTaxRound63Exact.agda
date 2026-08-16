module DASHI.Physics.Closure.NSTriadKNHHBadDirectProductTaxRound63Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- ROUND 63 A2 CONTRIBUTION
--
-- The HH-bad owner ultimately spends only the PRODUCT
--
--   C_* K_bad.
--
-- Optimizing C_* and K_bad separately is therefore unnecessarily rigid.  The
-- preferred physical estimate can be stated directly at the point where the
-- existing owner proof consumes it:
--
--   C_* Q_q^unmasked <= Lambda_bad D.
--
-- The exact gain calibration is 2 C_*, so this single product estimate yields
--
--   P_HHb <= (2 Lambda_bad) D
--
-- and hence an admissible owner with eta=2 Lambda_bad and zero data/critical
-- remainder.  The older pair of estimates C_q<=C_* and Q_q<=K_bad D remains a
-- sufficient route because it constructs Lambda_bad=C_* K_bad exactly.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNHHBadSingleThresholdSufficesRound47Exact as Selected
import DASHI.Physics.Closure.NSTriadKNHHBadNormalizedProfileRound45Exact as Profile
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedGainDensityRound39Exact as Gain
import DASHI.Physics.Closure.NSTriadKNHHBadOneDerivativeFactorizationRound44Exact as Factor
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedChargeSubchargeRound44Exact as Subcharge
import DASHI.Physics.Closure.NSTriadKNHHBadDirectOwnerRound43Exact as Direct
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHHBadSelectedProfileMultiplicityRound62Exact as Multiplicity

record PhysicalSelectedProfileProductInput
    (environment : Owner.TaxEnvironment)
    (effectiveViscosity : ℚ) : Set where
  field
    selectedProfile : Selected.SelectedThresholdHHBadNormalizedProfile effectiveViscosity
    viscosityNonnegative : 0ℚ ≤ effectiveViscosity

    badProduct : ℚ
    badProductNonnegative : 0ℚ ≤ badProduct

    ceilingTimesUnmaskedChargeBelowProductDissipation : ∀ shell →
      let profile = Selected.selectedThresholdToRound45Profile selectedProfile
          densityInput = Profile.canonicalOneDerivativeDensityAtShell profile shell
          certificate = Factor.asRound39InverseShellCertificate densityInput
          unmasked =
            Subcharge.sumCellUnmaskedViscousCharge
              effectiveViscosity shell (Gain.cells certificate)
      in
      Selected.selectedProfileCeiling selectedProfile * unmasked
      ≤ badProduct * Owner.dissipation environment

open PhysicalSelectedProfileProductInput public

productUniformProfile :
  ∀ {environment effectiveViscosity} →
  PhysicalSelectedProfileProductInput environment effectiveViscosity →
  Profile.UniformHHBadNormalizedProfile effectiveViscosity
productUniformProfile input =
  Selected.selectedThresholdToRound45Profile (selectedProfile input)

productEta :
  ∀ {environment effectiveViscosity} →
  PhysicalSelectedProfileProductInput environment effectiveViscosity → ℚ
productEta input = Sharp.two * badProduct input

productEtaNonnegative :
  ∀ {environment effectiveViscosity}
    (input : PhysicalSelectedProfileProductInput environment effectiveViscosity) →
  0ℚ ≤ productEta input
productEtaNonnegative input =
  let
    instance
      twoNN = nonNegative Sharp.twoNonnegative
      lambdaNN = nonNegative (badProductNonnegative input)
      productNN = ℚP.nonNeg*nonNeg⇒nonNeg Sharp.two (badProduct input)
  in
  ℚP.nonNegative⁻¹ (productEta input)

restrictedGainBelowProductDissipation :
  ∀ {environment effectiveViscosity}
    (input : PhysicalSelectedProfileProductInput environment effectiveViscosity) →
  ∀ shell →
  let profile = productUniformProfile input
      densityInput = Profile.canonicalOneDerivativeDensityAtShell profile shell
      certificate = Factor.asRound39InverseShellCertificate densityInput
  in
  Gain.sumCellGain (Gain.cells certificate)
  ≤ productEta input * Owner.dissipation environment
restrictedGainBelowProductDissipation
    {environment} {effectiveViscosity} input shell =
  let
    profile = productUniformProfile input
    densityInput = Profile.canonicalOneDerivativeDensityAtShell profile shell
    certificate = Factor.asRound39InverseShellCertificate densityInput
    gain = Gain.sumCellGain (Gain.cells certificate)
    charge = Gain.sumCellViscousCharge (Gain.cells certificate)
    unmasked =
      Subcharge.sumCellUnmaskedViscousCharge
        effectiveViscosity shell (Gain.cells certificate)
    target = Gain.inverseShellTarget certificate
    ceiling = Selected.selectedProfileCeiling (selectedProfile input)
    etaBase = Profile.canonicalHHBadEta profile
    lambda = badProduct input
    diss = Owner.dissipation environment

    targetNN = Gain.inverseShellTargetNonnegative certificate
    chargeNN = Gain.sumCellViscousChargeNonnegative (Gain.cells certificate)

    gainToTargetCharge : gain ≤ target * charge
    gainToTargetCharge =
      Gain.restrictedGainBelowInverseShellCharge
        effectiveViscosity shell certificate

    targetBelowEta : target ≤ etaBase
    targetBelowEta =
      Direct.requiredHHBadGainAtMostEta etaBase shell
        (Profile.canonicalHHBadEtaNonnegative profile)

    targetChargeToEtaCharge : target * charge ≤ etaBase * charge
    targetChargeToEtaCharge =
      L2.nonnegativeProductMonotone
        targetNN chargeNN
        (Profile.canonicalHHBadEtaNonnegative profile) chargeNN
        targetBelowEta ℚP.≤-refl

    chargeBelowUnmasked : charge ≤ unmasked
    chargeBelowUnmasked =
      Subcharge.restrictedCellChargeBelowUnmaskedCellCharge
        (Gain.cells certificate) (viscosityNonnegative input)

    etaChargeToEtaUnmasked : etaBase * charge ≤ etaBase * unmasked
    etaChargeToEtaUnmasked =
      let instance etaNN = nonNegative (Profile.canonicalHHBadEtaNonnegative profile)
      in ℚP.*-monoˡ-≤-nonNeg etaBase chargeBelowUnmasked

    etaUnmaskedMeaning : etaBase * unmasked ≡ Sharp.two * (ceiling * unmasked)
    etaUnmaskedMeaning = solve (ceiling ∷ unmasked ∷ [])

    scaledProduct :
      Sharp.two * (ceiling * unmasked)
      ≤ Sharp.two * (lambda * diss)
    scaledProduct =
      let instance twoNN = nonNegative Sharp.twoNonnegative
      in ℚP.*-monoˡ-≤-nonNeg Sharp.two
        (ceilingTimesUnmaskedChargeBelowProductDissipation input shell)

    endpoint : Sharp.two * (lambda * diss) ≡ productEta input * diss
    endpoint = solve (lambda ∷ diss ∷ [])
  in
  ℚP.≤-trans gainToTargetCharge
    (ℚP.≤-trans targetChargeToEtaCharge
      (ℚP.≤-trans etaChargeToEtaUnmasked
        (subst
          (λ left → left ≤ productEta input * diss)
          etaUnmaskedMeaning
          (subst
            (λ right → Sharp.two * (ceiling * unmasked) ≤ right)
            endpoint
            scaledProduct))))

physicalHHBadOwnerWithDirectProduct :
  ∀ {environment effectiveViscosity} →
  PhysicalSelectedProfileProductInput environment effectiveViscosity →
  Nat → Owner.AdmissibleOwnerEstimate environment
physicalHHBadOwnerWithDirectProduct {environment} input shell =
  let
    profile = productUniformProfile input
    densityInput = Profile.canonicalOneDerivativeDensityAtShell profile shell
    certificate = Factor.asRound39InverseShellCertificate densityInput
    eta = productEta input

    ownerBound :
      Gain.sumCellGain (Gain.cells certificate)
      ≤ eta * Owner.dissipation environment
        + 0ℚ + 0ℚ * Owner.integralCritical environment
    ownerBound =
      subst
        (λ upper → Gain.sumCellGain (Gain.cells certificate) ≤ upper)
        (sym (solve (eta ∷ Owner.dissipation environment ∷ [])))
        (restrictedGainBelowProductDissipation input shell)
  in
  Owner.admissible-owner-estimate
    Tax.HH-bad
    (Gain.sumCellGain (Gain.cells certificate))
    eta 0ℚ 0ℚ ownerBound

physicalHHBadOwnerEtaIsTwoBadProduct :
  ∀ {environment effectiveViscosity}
    (input : PhysicalSelectedProfileProductInput environment effectiveViscosity) →
  ∀ shell →
  Owner.eta (physicalHHBadOwnerWithDirectProduct input shell)
  ≡ Sharp.two * badProduct input
physicalHHBadOwnerEtaIsTwoBadProduct input shell = refl

multiplicityInputToDirectProduct :
  ∀ {environment effectiveViscosity} →
  Multiplicity.PhysicalSelectedProfileMultiplicityInput environment effectiveViscosity →
  PhysicalSelectedProfileProductInput environment effectiveViscosity
multiplicityInputToDirectProduct input = record
  { selectedProfile = Multiplicity.selectedProfile input
  ; viscosityNonnegative = Multiplicity.viscosityNonnegative input
  ; badProduct =
      Selected.selectedProfileCeiling (Multiplicity.selectedProfile input)
      * Multiplicity.badChargeMultiplicity input
  ; badProductNonnegative =
      let
        ceiling = Selected.selectedProfileCeiling (Multiplicity.selectedProfile input)
        k = Multiplicity.badChargeMultiplicity input
        instance
          ceilingNN = nonNegative
            (Selected.selectedProfileCeilingNonnegative
              (Multiplicity.selectedProfile input))
          kNN = nonNegative (Multiplicity.badChargeMultiplicityNonnegative input)
          productNN = ℚP.nonNeg*nonNeg⇒nonNeg ceiling k
      in
      ℚP.nonNegative⁻¹ (ceiling * k)
  ; ceilingTimesUnmaskedChargeBelowProductDissipation = λ shell →
      let
        selected = Multiplicity.selectedProfile input
        profile = Selected.selectedThresholdToRound45Profile selected
        densityInput = Profile.canonicalOneDerivativeDensityAtShell profile shell
        certificate = Factor.asRound39InverseShellCertificate densityInput
        unmasked =
          Subcharge.sumCellUnmaskedViscousCharge
            effectiveViscosity shell (Gain.cells certificate)
        ceiling = Selected.selectedProfileCeiling selected
        k = Multiplicity.badChargeMultiplicity input
        diss = Owner.dissipation environment

        scaled : ceiling * unmasked ≤ ceiling * (k * diss)
        scaled =
          let instance ceilingNN =
                nonNegative (Selected.selectedProfileCeilingNonnegative selected)
          in
          ℚP.*-monoˡ-≤-nonNeg ceiling
            (Multiplicity.unmaskedChargeBelowMultiplicityDissipation input shell)

        endpoint : ceiling * (k * diss) ≡ (ceiling * k) * diss
        endpoint = solve (ceiling ∷ k ∷ diss ∷ [])
      in
      subst
        (λ right → ceiling * unmasked ≤ right)
        endpoint
        scaled
  }

hhBadProductIsPrimaryOptimizationVariable : Bool
hhBadProductIsPrimaryOptimizationVariable = true

oldCeilingTimesMultiplicityConstructsProductRoute : Bool
oldCeilingTimesMultiplicityConstructsProductRoute = true

hhBadProductIsPrimaryOptimizationVariableIsTrue :
  hhBadProductIsPrimaryOptimizationVariable ≡ true
hhBadProductIsPrimaryOptimizationVariableIsTrue = refl

oldCeilingTimesMultiplicityConstructsProductRouteIsTrue :
  oldCeilingTimesMultiplicityConstructsProductRoute ≡ true
oldCeilingTimesMultiplicityConstructsProductRouteIsTrue = refl
