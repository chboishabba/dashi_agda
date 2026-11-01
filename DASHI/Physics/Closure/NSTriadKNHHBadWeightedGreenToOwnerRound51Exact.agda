module DASHI.Physics.Closure.NSTriadKNHHBadWeightedGreenToOwnerRound51Exact where

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
-- Route C is now a real consumer path.  The physical normalized gain need only
-- satisfy
--
--   2^q g_q <= C_q,
--
-- while C_q obeys the variable recurrence and its exact weighted Green response
-- is uniformly bounded by B.  Then
--
--   2^q g_q <= C_q <= C_0 + B,
--
-- and the existing selected-threshold owner is obtained with exact tax
--
--   eta_HHb = 2 (C_0 + B).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedGainDensityRound39Exact as Gain
import DASHI.Physics.Closure.NSTriadKNHHBadOneDerivativeFactorizationRound44Exact as Factor
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedChargeSubchargeRound44Exact as Subcharge
import DASHI.Physics.Closure.NSTriadKNHHBadNormalizedProfileRound45Exact as Profile
import DASHI.Physics.Closure.NSTriadKNHHBadSingleThresholdSufficesRound47Exact as Selected
import DASHI.Physics.Closure.NSTriadKNHHBadWeightedGreenForcingRound51Exact as Green

record WeightedGreenLiteralGainBridge
    (effectiveViscosity : ℚ)
    (recurrenceInput : Green.VariableGreenRecurrence) : Set where
  field
    selectedThreshold : Threshold.PositiveThreshold
    density : Nat → ℚ
    densityNonnegative : ∀ shell → 0ℚ ≤ density shell
    cells : ∀ shell →
      List (Gain.RestrictedGainDensityCell
        effectiveViscosity (density shell) shell)

    normalizedGainBelowDefectProfile : ∀ shell →
      Factor.scaleFreeDensityCoefficient (density shell) shell
      ≤ Green.profile recurrenceInput shell

open WeightedGreenLiteralGainBridge public

weightedGreenCeiling :
  ∀ {input} → Green.UniformWeightedGreenBound input → ℚ
weightedGreenCeiling {input} bound =
  Green.profile input zero + Green.weightedBudget bound

weightedGreenCeilingNonnegative :
  ∀ {input}
    (bound : Green.UniformWeightedGreenBound input) →
  0ℚ ≤ weightedGreenCeiling bound
weightedGreenCeilingNonnegative {input} bound =
  ℚP.+-mono-≤
    (Green.profileNonnegative input zero)
    (Green.weightedBudgetNonnegative bound)

weightedGreenToSelectedProfile :
  ∀ {effectiveViscosity recurrenceInput} →
  (bridge : WeightedGreenLiteralGainBridge
    effectiveViscosity recurrenceInput) →
  (bound : Green.UniformWeightedGreenBound recurrenceInput) →
  Selected.SelectedThresholdHHBadNormalizedProfile effectiveViscosity
weightedGreenToSelectedProfile {recurrenceInput = input} bridge bound = record
  { selectedThreshold = selectedThreshold bridge
  ; density = density bridge
  ; densityNonnegative = densityNonnegative bridge
  ; cells = cells bridge
  ; selectedProfileCeiling = weightedGreenCeiling bound
  ; selectedProfileCeilingNonnegative = weightedGreenCeilingNonnegative bound
  ; normalizedCoefficientBelowSelectedCeiling = λ shell →
      ℚP.≤-trans
        (normalizedGainBelowDefectProfile bridge shell)
        (Green.profileBelowBasePlusWeightedBudget input bound shell)
  }

record PhysicalWeightedGreenHHBadOwnerInput
    (environment : Owner.TaxEnvironment)
    (effectiveViscosity : ℚ)
    (recurrenceInput : Green.VariableGreenRecurrence) : Set where
  field
    bridge : WeightedGreenLiteralGainBridge
      effectiveViscosity recurrenceInput
    weightedBound : Green.UniformWeightedGreenBound recurrenceInput
    viscosityNonnegative : 0ℚ ≤ effectiveViscosity

    unmaskedChargeBelowPhysicalDissipation : ∀ shell →
      Subcharge.sumCellUnmaskedViscousCharge
        effectiveViscosity shell
        (Gain.cells
          (Factor.asRound39InverseShellCertificate
            (Profile.canonicalOneDerivativeDensityAtShell
              (Selected.selectedThresholdToRound45Profile
                (weightedGreenToSelectedProfile bridge weightedBound))
              shell)))
      ≤ Owner.dissipation environment

open PhysicalWeightedGreenHHBadOwnerInput public

asPhysicalSelectedThresholdProfile :
  ∀ {environment effectiveViscosity recurrenceInput} →
  PhysicalWeightedGreenHHBadOwnerInput
    environment effectiveViscosity recurrenceInput →
  Selected.PhysicalSelectedThresholdHHBadOwnerProfile
    environment effectiveViscosity
asPhysicalSelectedThresholdProfile input = record
  { selectedProfile =
      weightedGreenToSelectedProfile
        (bridge input)
        (weightedBound input)
  ; viscosityNonnegative = viscosityNonnegative input
  ; selectedUnmaskedChargeBelowPhysicalDissipation =
      unmaskedChargeBelowPhysicalDissipation input
  }

physicalHHBadOwnerFromWeightedGreen :
  ∀ {environment effectiveViscosity recurrenceInput} →
  PhysicalWeightedGreenHHBadOwnerInput
    environment effectiveViscosity recurrenceInput →
  Nat → Owner.AdmissibleOwnerEstimate environment
physicalHHBadOwnerFromWeightedGreen input =
  Selected.physicalHHBadOwnerFromOneSelectedThreshold
    (asPhysicalSelectedThresholdProfile input)

physicalHHBadWeightedGreenOwnerEtaExact :
  ∀ {environment effectiveViscosity recurrenceInput}
    (input : PhysicalWeightedGreenHHBadOwnerInput
      environment effectiveViscosity recurrenceInput) →
  ∀ shell →
  Owner.eta (physicalHHBadOwnerFromWeightedGreen input shell)
  ≡ Sharp.two * weightedGreenCeiling (weightedBound input)
physicalHHBadWeightedGreenOwnerEtaExact input shell =
  Profile.physicalHHBadOwnerEtaIsTwiceProfileCeiling
    (Selected.selectedThresholdToPhysicalRound45Profile
      (asPhysicalSelectedThresholdProfile input))
    shell

weightedGreenRouteFeedsMatureHHBadOwner : Bool
weightedGreenRouteFeedsMatureHHBadOwner = true

physicalWeightedGreenBridgeConstructed : Bool
physicalWeightedGreenBridgeConstructed = false

weightedGreenRouteFeedsMatureHHBadOwnerIsTrue :
  weightedGreenRouteFeedsMatureHHBadOwner ≡ true
weightedGreenRouteFeedsMatureHHBadOwnerIsTrue = refl
