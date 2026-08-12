module DASHI.Physics.Closure.NSTriadKNHHBadSummableForcingToOwnerRound50Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- Make the Round-50 fallback route a real consumer path rather than a side
-- lemma. If the literal normalized gain-density coefficient is the SAME
-- profile C_q that obeys borderline inheritance plus a bounded forcing prefix,
-- then the ceiling
--
--   M_sum = C_0 + B_force
--
-- feeds directly into the existing selected-threshold HH-bad owner, with the
-- exact tax
--
--   eta_HHb = 2 M_sum.
--
-- Thus strict uniform alpha<1 is not required by the owner architecture itself.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedGainDensityRound39Exact as Gain
import DASHI.Physics.Closure.NSTriadKNHHBadOneDerivativeFactorizationRound44Exact as Factor
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedChargeSubchargeRound44Exact as Subcharge
import DASHI.Physics.Closure.NSTriadKNHHBadNormalizedProfileRound45Exact as Profile
import DASHI.Physics.Closure.NSTriadKNHHBadSingleThresholdSufficesRound47Exact as Selected
import DASHI.Physics.Closure.NSTriadKNHHBadSummableForcingRound50Exact as Sum

record SummableForcingLiteralDensityBridge
    (effectiveViscosity : ℚ)
    (summableInput : Sum.BorderlineSummableForcing) : Set where
  field
    selectedThreshold : Threshold.PositiveThreshold
    density : Nat → ℚ
    densityNonnegative : ∀ shell → 0ℚ ≤ density shell
    cells : ∀ shell →
      List (Gain.RestrictedGainDensityCell
        effectiveViscosity (density shell) shell)

    normalizedDensityIsSummableProfile : ∀ shell →
      Factor.scaleFreeDensityCoefficient (density shell) shell
      ≡ Sum.profile summableInput shell

open SummableForcingLiteralDensityBridge public

summableCeiling : Sum.BorderlineSummableForcing → ℚ
summableCeiling input =
  Sum.profile input zero + Sum.totalForcingBudget input

summableCeilingNonnegative :
  (input : Sum.BorderlineSummableForcing) →
  (baseNonnegative : 0ℚ ≤ Sum.profile input zero) →
  0ℚ ≤ summableCeiling input
summableCeilingNonnegative input baseNN =
  ℚP.+-mono-≤ baseNN (Sum.totalForcingBudgetNonnegative input)

summableForcingToSelectedProfile :
  ∀ {effectiveViscosity summableInput} →
  (bridge : SummableForcingLiteralDensityBridge
    effectiveViscosity summableInput) →
  (prefix : Sum.PrefixSummable summableInput) →
  (baseNonnegative : 0ℚ ≤ Sum.profile summableInput zero) →
  Selected.SelectedThresholdHHBadNormalizedProfile effectiveViscosity
summableForcingToSelectedProfile {summableInput = input}
    bridge prefix baseNN = record
  { selectedThreshold = selectedThreshold bridge
  ; density = density bridge
  ; densityNonnegative = densityNonnegative bridge
  ; cells = cells bridge
  ; selectedProfileCeiling = summableCeiling input
  ; selectedProfileCeilingNonnegative = summableCeilingNonnegative input baseNN
  ; normalizedCoefficientBelowSelectedCeiling = λ shell →
      subst
        (λ normalized → normalized ≤ summableCeiling input)
        (sym (normalizedDensityIsSummableProfile bridge shell))
        (Sum.profileBelowBasePlusBudget input prefix shell)
  }

record PhysicalSummableForcingHHBadOwnerInput
    (environment : Owner.TaxEnvironment)
    (effectiveViscosity : ℚ)
    (summableInput : Sum.BorderlineSummableForcing) : Set where
  field
    bridge : SummableForcingLiteralDensityBridge
      effectiveViscosity summableInput
    prefixSummable : Sum.PrefixSummable summableInput
    normalizedBaseNonnegative : 0ℚ ≤ Sum.profile summableInput zero
    viscosityNonnegative : 0ℚ ≤ effectiveViscosity

    unmaskedChargeBelowPhysicalDissipation : ∀ shell →
      Subcharge.sumCellUnmaskedViscousCharge
        effectiveViscosity shell
        (Gain.cells
          (Factor.asRound39InverseShellCertificate
            (Profile.canonicalOneDerivativeDensityAtShell
              (Selected.selectedThresholdToRound45Profile
                (summableForcingToSelectedProfile
                  bridge prefixSummable normalizedBaseNonnegative))
              shell)))
      ≤ Owner.dissipation environment

open PhysicalSummableForcingHHBadOwnerInput public

asPhysicalSelectedThresholdProfile :
  ∀ {environment effectiveViscosity summableInput} →
  PhysicalSummableForcingHHBadOwnerInput
    environment effectiveViscosity summableInput →
  Selected.PhysicalSelectedThresholdHHBadOwnerProfile
    environment effectiveViscosity
asPhysicalSelectedThresholdProfile input = record
  { selectedProfile =
      summableForcingToSelectedProfile
        (bridge input)
        (prefixSummable input)
        (normalizedBaseNonnegative input)
  ; viscosityNonnegative = viscosityNonnegative input
  ; selectedUnmaskedChargeBelowPhysicalDissipation =
      unmaskedChargeBelowPhysicalDissipation input
  }

physicalHHBadOwnerFromSummableForcing :
  ∀ {environment effectiveViscosity summableInput} →
  PhysicalSummableForcingHHBadOwnerInput
    environment effectiveViscosity summableInput →
  Nat → Owner.AdmissibleOwnerEstimate environment
physicalHHBadOwnerFromSummableForcing input =
  Selected.physicalHHBadOwnerFromOneSelectedThreshold
    (asPhysicalSelectedThresholdProfile input)

physicalHHBadSummableOwnerEtaExact :
  ∀ {environment effectiveViscosity summableInput}
    (input : PhysicalSummableForcingHHBadOwnerInput
      environment effectiveViscosity summableInput) →
  ∀ shell →
  Owner.eta (physicalHHBadOwnerFromSummableForcing input shell)
  ≡ Sharp.two * summableCeiling summableInput
physicalHHBadSummableOwnerEtaExact input shell =
  Profile.physicalHHBadOwnerEtaIsTwiceProfileCeiling
    (Selected.selectedThresholdToPhysicalRound45Profile
      (asPhysicalSelectedThresholdProfile input))
    shell

summableForcingRouteFeedsMatureHHBadOwner : Bool
summableForcingRouteFeedsMatureHHBadOwner = true

physicalSummableForcingDensityBridgeConstructed : Bool
physicalSummableForcingDensityBridgeConstructed = false

summableForcingRouteFeedsMatureHHBadOwnerIsTrue :
  summableForcingRouteFeedsMatureHHBadOwner ≡ true
summableForcingRouteFeedsMatureHHBadOwnerIsTrue = refl
