module DASHI.Physics.Closure.NSTriadKNHHBadSingleThresholdSufficesRound47Exact where

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
-- Audit the ACTUAL Round-45 owner consumer before demanding global delta
-- uniformity.  That consumer needs one shell-uniform normalized profile, but
-- it contains no quantifier over every positive threshold.  Therefore a proof
-- may choose one physically admissible coherence threshold delta_* and prove
--
--   C_q(delta_*) <= C_*(delta_*)   for all q,
--
-- then feed that selected-threshold profile directly into the mature HH-bad
-- owner reducer.  Uniformity as delta -> 0 is strictly stronger than the owner
-- architecture currently consumes.
--
-- This does not pick a physically valid delta_*; admissibility still belongs to
-- the geometric/PDE producer.  It removes an unnecessary global quantifier from
-- the formal target.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedGainDensityRound39Exact as Gain
import DASHI.Physics.Closure.NSTriadKNHHBadOneDerivativeFactorizationRound44Exact as Factor
import DASHI.Physics.Closure.NSTriadKNHHBadNormalizedProfileRound45Exact as Profile
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedChargeSubchargeRound44Exact as Subcharge

record SelectedThresholdHHBadNormalizedProfile
    (effectiveViscosity : ℚ) : Set where
  field
    selectedThreshold : Threshold.PositiveThreshold

    density : Nat → ℚ
    densityNonnegative : ∀ shell → 0ℚ ≤ density shell
    cells : ∀ shell →
      List (Gain.RestrictedGainDensityCell
        effectiveViscosity (density shell) shell)

    selectedProfileCeiling : ℚ
    selectedProfileCeilingNonnegative : 0ℚ ≤ selectedProfileCeiling
    normalizedCoefficientBelowSelectedCeiling : ∀ shell →
      Factor.scaleFreeDensityCoefficient (density shell) shell
      ≤ selectedProfileCeiling

open SelectedThresholdHHBadNormalizedProfile public

selectedThresholdToRound45Profile :
  ∀ {effectiveViscosity} →
  SelectedThresholdHHBadNormalizedProfile effectiveViscosity →
  Profile.UniformHHBadNormalizedProfile effectiveViscosity
selectedThresholdToRound45Profile selected = record
  { density = density selected
  ; densityNonnegative = densityNonnegative selected
  ; cells = cells selected
  ; profileCeiling = selectedProfileCeiling selected
  ; profileCeilingNonnegative = selectedProfileCeilingNonnegative selected
  ; normalizedCoefficientBelowCeiling =
      normalizedCoefficientBelowSelectedCeiling selected
  }

record PhysicalSelectedThresholdHHBadOwnerProfile
    (environment : Owner.TaxEnvironment)
    (effectiveViscosity : ℚ) : Set where
  field
    selectedProfile : SelectedThresholdHHBadNormalizedProfile effectiveViscosity
    viscosityNonnegative : 0ℚ ≤ effectiveViscosity

    selectedUnmaskedChargeBelowPhysicalDissipation : ∀ shell →
      Subcharge.sumCellUnmaskedViscousCharge
        effectiveViscosity shell
        (Gain.cells
          (Factor.asRound39InverseShellCertificate
            (Profile.canonicalOneDerivativeDensityAtShell
              (selectedThresholdToRound45Profile selectedProfile)
              shell)))
      ≤ Owner.dissipation environment

open PhysicalSelectedThresholdHHBadOwnerProfile public

selectedThresholdToPhysicalRound45Profile :
  ∀ {environment effectiveViscosity} →
  PhysicalSelectedThresholdHHBadOwnerProfile environment effectiveViscosity →
  Profile.PhysicalUniformHHBadOwnerProfile environment effectiveViscosity
selectedThresholdToPhysicalRound45Profile physical = record
  { normalizedProfile =
      selectedThresholdToRound45Profile (selectedProfile physical)
  ; viscosityNonnegative = viscosityNonnegative physical
  ; unmaskedChargeBelowPhysicalDissipation =
      selectedUnmaskedChargeBelowPhysicalDissipation physical
  }

physicalHHBadOwnerFromOneSelectedThreshold :
  ∀ {environment effectiveViscosity} →
  PhysicalSelectedThresholdHHBadOwnerProfile environment effectiveViscosity →
  Nat → Owner.AdmissibleOwnerEstimate environment
physicalHHBadOwnerFromOneSelectedThreshold physical =
  Profile.physicalHHBadOwnerAtShell
    (selectedThresholdToPhysicalRound45Profile physical)

oneSelectedThresholdSufficesForCurrentHHBadOwnerConsumer : Bool
oneSelectedThresholdSufficesForCurrentHHBadOwnerConsumer = true

globalDeltaUniformityRequiredByCurrentOwnerConsumer : Bool
globalDeltaUniformityRequiredByCurrentOwnerConsumer = false

oneSelectedThresholdSufficesForCurrentHHBadOwnerConsumerIsTrue :
  oneSelectedThresholdSufficesForCurrentHHBadOwnerConsumer ≡ true
oneSelectedThresholdSufficesForCurrentHHBadOwnerConsumerIsTrue = refl

globalDeltaUniformityRequiredByCurrentOwnerConsumerIsFalse :
  globalDeltaUniformityRequiredByCurrentOwnerConsumer ≡ false
globalDeltaUniformityRequiredByCurrentOwnerConsumerIsFalse = refl
