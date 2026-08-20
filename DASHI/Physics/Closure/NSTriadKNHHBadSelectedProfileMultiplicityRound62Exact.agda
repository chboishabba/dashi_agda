module DASHI.Physics.Closure.NSTriadKNHHBadSelectedProfileMultiplicityRound62Exact where

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
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND 62 CONTRIBUTION
--
-- Round61 allowed a physical charge multiplicity K_bad but routed it through
-- the older affine recurrence object.  Round62's direct component-headroom
-- theorem produces the mature SelectedThresholdHHBadNormalizedProfile without
-- any alpha/beta recurrence.  This file removes that obsolete dependency.
--
-- For a selected profile with ceiling C_* the exact gain calibration is 2 C_*.
-- If the literal unmasked shell charge obeys
--
--   Q_q <= K_bad D,
--
-- then the grouped gain obeys
--
--   P_HHb <= (2 C_* K_bad) D.
--
-- Thus the direct A path feeds the admissible nine-owner language with eta
-- exactly 2 C_* K_bad and zero data/critical remainder.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
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

record PhysicalSelectedProfileMultiplicityInput
    (environment : Owner.TaxEnvironment)
    (effectiveViscosity : ℚ) : Set where
  field
    selectedProfile : Selected.SelectedThresholdHHBadNormalizedProfile effectiveViscosity
    viscosityNonnegative : 0ℚ ≤ effectiveViscosity

    badChargeMultiplicity : ℚ
    badChargeMultiplicityNonnegative : 0ℚ ≤ badChargeMultiplicity

    unmaskedChargeBelowMultiplicityDissipation : ∀ shell →
      Subcharge.sumCellUnmaskedViscousCharge
        effectiveViscosity shell
        (Gain.cells
          (Factor.asRound39InverseShellCertificate
            (Profile.canonicalOneDerivativeDensityAtShell
              (Selected.selectedThresholdToRound45Profile selectedProfile)
              shell)))
      ≤ badChargeMultiplicity * Owner.dissipation environment

open PhysicalSelectedProfileMultiplicityInput public

baseUniformProfile :
  ∀ {environment effectiveViscosity} →
  PhysicalSelectedProfileMultiplicityInput environment effectiveViscosity →
  Profile.UniformHHBadNormalizedProfile effectiveViscosity
baseUniformProfile input =
  Selected.selectedThresholdToRound45Profile (selectedProfile input)

baseEta :
  ∀ {environment effectiveViscosity} →
  PhysicalSelectedProfileMultiplicityInput environment effectiveViscosity → ℚ
baseEta input = Profile.canonicalHHBadEta (baseUniformProfile input)

multiplicityEta :
  ∀ {environment effectiveViscosity} →
  PhysicalSelectedProfileMultiplicityInput environment effectiveViscosity → ℚ
multiplicityEta input = baseEta input * badChargeMultiplicity input

multiplicityEtaNonnegative :
  ∀ {environment effectiveViscosity}
    (input : PhysicalSelectedProfileMultiplicityInput
      environment effectiveViscosity) →
  0ℚ ≤ multiplicityEta input
multiplicityEtaNonnegative input =
  let
    etaNN = Profile.canonicalHHBadEtaNonnegative (baseUniformProfile input)
    kNN = badChargeMultiplicityNonnegative input
    instance
      etaNNI = nonNegative etaNN
      kNNI = nonNegative kNN
      productNNI =
        ℚP.nonNeg*nonNeg⇒nonNeg (baseEta input) (badChargeMultiplicity input)
  in
  ℚP.nonNegative⁻¹ (multiplicityEta input)

restrictedGainBelowMultiplicityDissipation :
  ∀ {environment effectiveViscosity}
    (input : PhysicalSelectedProfileMultiplicityInput
      environment effectiveViscosity) →
  ∀ shell →
  let densityInput =
        Profile.canonicalOneDerivativeDensityAtShell
          (baseUniformProfile input) shell
      certificate = Factor.asRound39InverseShellCertificate densityInput
  in
  Gain.sumCellGain (Gain.cells certificate)
  ≤ multiplicityEta input * Owner.dissipation environment
restrictedGainBelowMultiplicityDissipation
    {environment} {effectiveViscosity} input shell =
  let
    profile = baseUniformProfile input
    eta = baseEta input
    k = badChargeMultiplicity input
    densityInput = Profile.canonicalOneDerivativeDensityAtShell profile shell
    certificate = Factor.asRound39InverseShellCertificate densityInput
    gain = Gain.sumCellGain (Gain.cells certificate)
    charge = Gain.sumCellViscousCharge (Gain.cells certificate)
    unmasked =
      Subcharge.sumCellUnmaskedViscousCharge
        effectiveViscosity shell (Gain.cells certificate)
    target = Gain.inverseShellTarget certificate

    targetNN = Gain.inverseShellTargetNonnegative certificate
    chargeNN = Gain.sumCellViscousChargeNonnegative (Gain.cells certificate)

    gainToTargetCharge : gain ≤ target * charge
    gainToTargetCharge =
      Gain.restrictedGainBelowInverseShellCharge
        effectiveViscosity shell certificate

    targetBelowEta : target ≤ eta
    targetBelowEta =
      Direct.requiredHHBadGainAtMostEta eta shell
        (Profile.canonicalHHBadEtaNonnegative profile)

    targetChargeToEtaCharge : target * charge ≤ eta * charge
    targetChargeToEtaCharge =
      L2.nonnegativeProductMonotone
        targetNN chargeNN
        (Profile.canonicalHHBadEtaNonnegative profile) chargeNN
        targetBelowEta ℚP.≤-refl

    chargeBelowUnmasked : charge ≤ unmasked
    chargeBelowUnmasked =
      Subcharge.restrictedCellChargeBelowUnmaskedCellCharge
        (Gain.cells certificate) (viscosityNonnegative input)

    etaChargeBelowEtaUnmasked : eta * charge ≤ eta * unmasked
    etaChargeBelowEtaUnmasked =
      let instance etaNNI =
        nonNegative (Profile.canonicalHHBadEtaNonnegative profile)
      in ℚP.*-monoˡ-≤-nonNeg eta chargeBelowUnmasked

    etaUnmaskedBelowEtaKD :
      eta * unmasked ≤ eta * (k * Owner.dissipation environment)
    etaUnmaskedBelowEtaKD =
      let instance etaNNI =
        nonNegative (Profile.canonicalHHBadEtaNonnegative profile)
      in ℚP.*-monoˡ-≤-nonNeg eta
        (unmaskedChargeBelowMultiplicityDissipation input shell)

    endpoint :
      eta * (k * Owner.dissipation environment)
      ≡ multiplicityEta input * Owner.dissipation environment
    endpoint = solve (eta ∷ k ∷ Owner.dissipation environment ∷ [])
  in
  ℚP.≤-trans gainToTargetCharge
    (ℚP.≤-trans targetChargeToEtaCharge
      (ℚP.≤-trans etaChargeBelowEtaUnmasked
        (subst
          (λ upper → eta * unmasked ≤ upper)
          endpoint
          etaUnmaskedBelowEtaKD)))

physicalHHBadOwnerWithMultiplicity :
  ∀ {environment effectiveViscosity} →
  PhysicalSelectedProfileMultiplicityInput environment effectiveViscosity →
  Nat → Owner.AdmissibleOwnerEstimate environment
physicalHHBadOwnerWithMultiplicity {environment} input shell =
  let
    profile = baseUniformProfile input
    densityInput = Profile.canonicalOneDerivativeDensityAtShell profile shell
    certificate = Factor.asRound39InverseShellCertificate densityInput
    eta = multiplicityEta input

    ownerBound :
      Gain.sumCellGain (Gain.cells certificate)
      ≤ eta * Owner.dissipation environment
        + 0ℚ + 0ℚ * Owner.integralCritical environment
    ownerBound =
      subst
        (λ upper → Gain.sumCellGain (Gain.cells certificate) ≤ upper)
        (sym (solve (eta ∷ Owner.dissipation environment ∷ [])))
        (restrictedGainBelowMultiplicityDissipation input shell)
  in
  Owner.admissible-owner-estimate
    Tax.HH-bad
    (Gain.sumCellGain (Gain.cells certificate))
    eta 0ℚ 0ℚ ownerBound

physicalHHBadOwnerEtaIsTwoCeilingTimesMultiplicity :
  ∀ {environment effectiveViscosity}
    (input : PhysicalSelectedProfileMultiplicityInput
      environment effectiveViscosity) →
  ∀ shell →
  Owner.eta (physicalHHBadOwnerWithMultiplicity input shell)
  ≡ Sharp.two
      * Selected.selectedProfileCeiling (selectedProfile input)
      * badChargeMultiplicity input
physicalHHBadOwnerEtaIsTwoCeilingTimesMultiplicity input shell = refl

directSelectedProfileFeedsMultiplicityOwner : Bool
directSelectedProfileFeedsMultiplicityOwner = true

directSelectedProfileFeedsMultiplicityOwnerIsTrue :
  directSelectedProfileFeedsMultiplicityOwner ≡ true
directSelectedProfileFeedsMultiplicityOwnerIsTrue = refl
