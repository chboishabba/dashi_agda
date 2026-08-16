module DASHI.Physics.Closure.NSTriadKNHHBadDominatedRecurrenceMultiplicityRound61Exact where

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
-- ROUND 61 CONTRIBUTION
--
-- Two unnecessary strengthenings are removed from the HH-bad physical bridge.
--
-- (1) The owner never needs equality between the literal normalized density
--     2^q g_q and the selected Duhamel defect C_q.  Domination is enough:
--
--       2^q g_q <= C_q <= C_*.
--
-- (2) The literal unmasked cell charge need not have multiplicity one.  If
--
--       charge_q <= K_bad D,
--
--     the same proof gives the exact owner tax
--
--       eta_HHb = (2 C_*) K_bad.
--
-- This is the A3 shape requested by the physical cutset.  K_bad=1 is a
-- special case, not an assumption baked into the theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedGainDensityRound39Exact as Gain
import DASHI.Physics.Closure.NSTriadKNHHBadOneDerivativeFactorizationRound44Exact as Factor
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedChargeSubchargeRound44Exact as Subcharge
import DASHI.Physics.Closure.NSTriadKNHHBadDirectOwnerRound43Exact as Direct
import DASHI.Physics.Closure.NSTriadKNHHBadDefectRecurrenceNormalizationRound46Exact as Defect
import DASHI.Physics.Closure.NSTriadKNHHBadSelectedThresholdRecurrenceRound47Exact as Recurrence
import DASHI.Physics.Closure.NSTriadKNHHBadSingleThresholdSufficesRound47Exact as Selected
import DASHI.Physics.Closure.NSTriadKNHHBadNormalizedProfileRound45Exact as Profile

record SelectedRecurrenceLiteralDensityDominationBridge
    (effectiveViscosity : ℚ)
    (recurrence : Recurrence.SelectedThresholdDefectRecurrence) : Set where
  field
    density : Nat → ℚ
    densityNonnegative : ∀ shell → 0ℚ ≤ density shell

    cells : ∀ shell →
      List (Gain.RestrictedGainDensityCell
        effectiveViscosity (density shell) shell)

    normalizedDensityBelowNormalizedDefect : ∀ shell →
      Factor.scaleFreeDensityCoefficient (density shell) shell
      ≤ Defect.normalizedDefectProfile
          (Recurrence.asPhysicalDefectRecurrence recurrence) shell

open SelectedRecurrenceLiteralDensityDominationBridge public

selectedRecurrenceToOwnerProfileFromDomination :
  ∀ {effectiveViscosity recurrence} →
  SelectedRecurrenceLiteralDensityDominationBridge
    effectiveViscosity recurrence →
  Selected.SelectedThresholdHHBadNormalizedProfile effectiveViscosity
selectedRecurrenceToOwnerProfileFromDomination
    {recurrence = recurrence} bridge = record
  { selectedThreshold = Recurrence.parameter recurrence
  ; density = density bridge
  ; densityNonnegative = densityNonnegative bridge
  ; cells = cells bridge
  ; selectedProfileCeiling = Recurrence.ceiling recurrence
  ; selectedProfileCeilingNonnegative = Recurrence.ceilingNonnegative recurrence
  ; normalizedCoefficientBelowSelectedCeiling = λ shell →
      ℚP.≤-trans
        (normalizedDensityBelowNormalizedDefect bridge shell)
        (Recurrence.selectedThresholdUniformShellCeiling recurrence shell)
  }

baseUniformProfile :
  ∀ {effectiveViscosity recurrence} →
  SelectedRecurrenceLiteralDensityDominationBridge
    effectiveViscosity recurrence →
  Profile.UniformHHBadNormalizedProfile effectiveViscosity
baseUniformProfile bridge =
  Selected.selectedThresholdToRound45Profile
    (selectedRecurrenceToOwnerProfileFromDomination bridge)

record PhysicalDominatedRecurrenceHHBadOwnerInput
    (environment : Owner.TaxEnvironment)
    (effectiveViscosity : ℚ)
    (recurrence : Recurrence.SelectedThresholdDefectRecurrence) : Set where
  field
    densityBridge :
      SelectedRecurrenceLiteralDensityDominationBridge
        effectiveViscosity recurrence

    viscosityNonnegative : 0ℚ ≤ effectiveViscosity

    badChargeMultiplicity : ℚ
    badChargeMultiplicityNonnegative : 0ℚ ≤ badChargeMultiplicity

    unmaskedChargeBelowMultiplicityDissipation : ∀ shell →
      Subcharge.sumCellUnmaskedViscousCharge
        effectiveViscosity shell
        (Gain.cells
          (Factor.asRound39InverseShellCertificate
            (Profile.canonicalOneDerivativeDensityAtShell
              (baseUniformProfile densityBridge) shell)))
      ≤ badChargeMultiplicity * Owner.dissipation environment

open PhysicalDominatedRecurrenceHHBadOwnerInput public

baseEta :
  ∀ {environment effectiveViscosity recurrence} →
  PhysicalDominatedRecurrenceHHBadOwnerInput
    environment effectiveViscosity recurrence → ℚ
baseEta input = Profile.canonicalHHBadEta (baseUniformProfile (densityBridge input))

multiplicityEta :
  ∀ {environment effectiveViscosity recurrence} →
  PhysicalDominatedRecurrenceHHBadOwnerInput
    environment effectiveViscosity recurrence → ℚ
multiplicityEta input = baseEta input * badChargeMultiplicity input

multiplicityEtaNonnegative :
  ∀ {environment effectiveViscosity recurrence}
    (input : PhysicalDominatedRecurrenceHHBadOwnerInput
      environment effectiveViscosity recurrence) →
  0ℚ ≤ multiplicityEta input
multiplicityEtaNonnegative input =
  let
    etaNN = Profile.canonicalHHBadEtaNonnegative
      (baseUniformProfile (densityBridge input))
    kNN = badChargeMultiplicityNonnegative input
    instance
      etaNNI = nonNegative etaNN
      kNNI = nonNegative kNN
      productNNI =
        ℚP.nonNeg*nonNeg⇒nonNeg (baseEta input) (badChargeMultiplicity input)
  in
  ℚP.nonNegative⁻¹ (multiplicityEta input)

restrictedGainBelowMultiplicityDissipation :
  ∀ {environment effectiveViscosity recurrence}
    (input : PhysicalDominatedRecurrenceHHBadOwnerInput
      environment effectiveViscosity recurrence) →
  ∀ shell →
  let densityInput =
        Profile.canonicalOneDerivativeDensityAtShell
          (baseUniformProfile (densityBridge input)) shell
      certificate = Factor.asRound39InverseShellCertificate densityInput
  in
  Gain.sumCellGain (Gain.cells certificate)
  ≤ multiplicityEta input * Owner.dissipation environment
restrictedGainBelowMultiplicityDissipation
    {environment} {effectiveViscosity} input shell =
  let
    profile = baseUniformProfile (densityBridge input)
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

    targetNN : 0ℚ ≤ target
    targetNN = Gain.inverseShellTargetNonnegative certificate

    chargeNN : 0ℚ ≤ charge
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
      let instance etaNNI = nonNegative (Profile.canonicalHHBadEtaNonnegative profile)
      in ℚP.*-monoˡ-≤-nonNeg eta chargeBelowUnmasked

    etaUnmaskedBelowEtaKD :
      eta * unmasked ≤ eta * (k * Owner.dissipation environment)
    etaUnmaskedBelowEtaKD =
      let instance etaNNI = nonNegative (Profile.canonicalHHBadEtaNonnegative profile)
      in ℚP.*-monoˡ-≤-nonNeg eta
        (unmaskedChargeBelowMultiplicityDissipation input shell)

    endpoint :
      eta * (k * Owner.dissipation environment)
      ≡ multiplicityEta input * Owner.dissipation environment
    endpoint = solve
      (eta ∷ k ∷ Owner.dissipation environment ∷ [])
  in
  ℚP.≤-trans gainToTargetCharge
    (ℚP.≤-trans targetChargeToEtaCharge
      (ℚP.≤-trans etaChargeBelowEtaUnmasked
        (subst
          (λ upper → eta * unmasked ≤ upper)
          endpoint
          etaUnmaskedBelowEtaKD)))

physicalHHBadOwnerWithMultiplicity :
  ∀ {environment effectiveViscosity recurrence} →
  PhysicalDominatedRecurrenceHHBadOwnerInput
    environment effectiveViscosity recurrence →
  Nat → Owner.AdmissibleOwnerEstimate environment
physicalHHBadOwnerWithMultiplicity {environment} input shell =
  let
    profile = baseUniformProfile (densityBridge input)
    densityInput = Profile.canonicalOneDerivativeDensityAtShell profile shell
    certificate = Factor.asRound39InverseShellCertificate densityInput
    eta = multiplicityEta input

    ownerBound :
      Gain.sumCellGain (Gain.cells certificate)
      ≤ eta * Owner.dissipation environment
        + 0ℚ
        + 0ℚ * Owner.integralCritical environment
    ownerBound =
      subst
        (λ upper → Gain.sumCellGain (Gain.cells certificate) ≤ upper)
        (sym (solve (eta ∷ Owner.dissipation environment ∷ [])))
        (restrictedGainBelowMultiplicityDissipation input shell)
  in
  Owner.admissible-owner-estimate
    Tax.HH-bad
    (Gain.sumCellGain (Gain.cells certificate))
    eta
    0ℚ
    0ℚ
    ownerBound

physicalHHBadOwnerEtaIsTwoCeilingTimesMultiplicity :
  ∀ {environment effectiveViscosity recurrence}
    (input : PhysicalDominatedRecurrenceHHBadOwnerInput
      environment effectiveViscosity recurrence) →
  ∀ shell →
  Owner.eta (physicalHHBadOwnerWithMultiplicity input shell)
  ≡ Profile.canonicalHHBadEta (baseUniformProfile (densityBridge input))
      * badChargeMultiplicity input
physicalHHBadOwnerEtaIsTwoCeilingTimesMultiplicity input shell = refl

normalizedDensityDominationSuffices : Bool
normalizedDensityDominationSuffices = true

badChargeMultiplicityPreserved : Bool
badChargeMultiplicityPreserved = true

normalizedDensityDominationSufficesIsTrue :
  normalizedDensityDominationSuffices ≡ true
normalizedDensityDominationSufficesIsTrue = refl

badChargeMultiplicityPreservedIsTrue :
  badChargeMultiplicityPreserved ≡ true
badChargeMultiplicityPreservedIsTrue = refl
