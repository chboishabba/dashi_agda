module DASHI.Physics.Closure.NSTriadKNHHBadSelectedRecurrenceToOwnerRound47Exact where

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
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- The selected-threshold recurrence controls a normalized defect observable,
-- while the mature Round-45 owner consumes the normalized literal gain-density
-- coefficient 2^q g_q.  They must be the SAME physical object before the
-- recurrence can pay the HH-bad tax.
--
-- This module isolates precisely that bridge.  If literal Round-39 cells have
-- density g_q and one proves
--
--   2^q g_q = delta_*^(-1) 2^q B_q,
--
-- shell by shell, then the selected recurrence ceiling M immediately constructs
-- the Round-47 selected-threshold owner profile.  Adding the already-isolated
-- unmasked-charge <= physical-dissipation theorem then constructs the mature
-- HH-bad owner at every shell with eta = 2M.
--
-- No equality between defect rate and gain density is postulated globally; it
-- is an explicit physical same-object input.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedGainDensityRound39Exact as Gain
import DASHI.Physics.Closure.NSTriadKNHHBadOneDerivativeFactorizationRound44Exact as Factor
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedChargeSubchargeRound44Exact as Subcharge
import DASHI.Physics.Closure.NSTriadKNHHBadSelectedThresholdRecurrenceRound47Exact as Recurrence
import DASHI.Physics.Closure.NSTriadKNHHBadSingleThresholdSufficesRound47Exact as Selected
import DASHI.Physics.Closure.NSTriadKNHHBadNormalizedProfileRound45Exact as Profile

record SelectedRecurrenceLiteralDensityBridge
    (effectiveViscosity : ℚ)
    (recurrence : Recurrence.SelectedThresholdDefectRecurrence) : Set where
  field
    density : Nat → ℚ
    densityNonnegative : ∀ shell → 0ℚ ≤ density shell

    cells : ∀ shell →
      List (Gain.RestrictedGainDensityCell
        effectiveViscosity (density shell) shell)

    normalizedDensityIsNormalizedDefect : ∀ shell →
      Factor.scaleFreeDensityCoefficient (density shell) shell
      ≡ DASHI.Physics.Closure.NSTriadKNHHBadDefectRecurrenceNormalizationRound46Exact.normalizedDefectProfile
          (Recurrence.asPhysicalDefectRecurrence recurrence) shell

open SelectedRecurrenceLiteralDensityBridge public

selectedRecurrenceToOwnerProfile :
  ∀ {effectiveViscosity recurrence} →
  SelectedRecurrenceLiteralDensityBridge effectiveViscosity recurrence →
  Selected.SelectedThresholdHHBadNormalizedProfile effectiveViscosity
selectedRecurrenceToOwnerProfile {recurrence = recurrence} bridge = record
  { selectedThreshold = Recurrence.parameter recurrence
  ; density = density bridge
  ; densityNonnegative = densityNonnegative bridge
  ; cells = cells bridge
  ; selectedProfileCeiling = Recurrence.ceiling recurrence
  ; selectedProfileCeilingNonnegative = Recurrence.ceilingNonnegative recurrence
  ; normalizedCoefficientBelowSelectedCeiling = λ shell →
      subst
        (λ normalized → normalized ≤ Recurrence.ceiling recurrence)
        (normalizedDensityIsNormalizedDefect bridge shell)
        (Recurrence.selectedThresholdUniformShellCeiling recurrence shell)
  }

record PhysicalSelectedRecurrenceHHBadOwnerInput
    (environment : Owner.TaxEnvironment)
    (effectiveViscosity : ℚ)
    (recurrence : Recurrence.SelectedThresholdDefectRecurrence) : Set where
  field
    densityBridge :
      SelectedRecurrenceLiteralDensityBridge effectiveViscosity recurrence
    viscosityNonnegative : 0ℚ ≤ effectiveViscosity

    unmaskedChargeBelowPhysicalDissipation : ∀ shell →
      Subcharge.sumCellUnmaskedViscousCharge
        effectiveViscosity shell
        (Gain.cells
          (Factor.asRound39InverseShellCertificate
            (Profile.canonicalOneDerivativeDensityAtShell
              (Selected.selectedThresholdToRound45Profile
                (selectedRecurrenceToOwnerProfile densityBridge))
              shell)))
      ≤ Owner.dissipation environment

open PhysicalSelectedRecurrenceHHBadOwnerInput public

asPhysicalSelectedThresholdOwnerProfile :
  ∀ {environment effectiveViscosity recurrence} →
  PhysicalSelectedRecurrenceHHBadOwnerInput
    environment effectiveViscosity recurrence →
  Selected.PhysicalSelectedThresholdHHBadOwnerProfile
    environment effectiveViscosity
asPhysicalSelectedThresholdOwnerProfile input = record
  { selectedProfile = selectedRecurrenceToOwnerProfile (densityBridge input)
  ; viscosityNonnegative = viscosityNonnegative input
  ; selectedUnmaskedChargeBelowPhysicalDissipation =
      unmaskedChargeBelowPhysicalDissipation input
  }

physicalHHBadOwnerFromSelectedRecurrence :
  ∀ {environment effectiveViscosity recurrence} →
  PhysicalSelectedRecurrenceHHBadOwnerInput
    environment effectiveViscosity recurrence →
  Nat → Owner.AdmissibleOwnerEstimate environment
physicalHHBadOwnerFromSelectedRecurrence input =
  Selected.physicalHHBadOwnerFromOneSelectedThreshold
    (asPhysicalSelectedThresholdOwnerProfile input)

selectedRecurrenceToOwnerBridgeExact : Bool
selectedRecurrenceToOwnerBridgeExact = true

physicalNormalizedDensityDefectIdentificationConstructed : Bool
physicalNormalizedDensityDefectIdentificationConstructed = false

selectedRecurrenceToOwnerBridgeExactIsTrue :
  selectedRecurrenceToOwnerBridgeExact ≡ true
selectedRecurrenceToOwnerBridgeExactIsTrue = refl
