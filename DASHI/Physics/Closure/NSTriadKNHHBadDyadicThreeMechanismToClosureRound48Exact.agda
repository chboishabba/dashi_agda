module DASHI.Physics.Closure.NSTriadKNHHBadDyadicThreeMechanismToClosureRound48Exact where

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
-- Compose the actual Round-48 HH-bad research surface all the way to the
-- mature owner.  The caller must supply only genuinely physical statements:
--
-- * selected-threshold three-mechanism shell transport;
-- * literal normalized gain-density = normalized defect, shell by shell;
-- * viscosity nonnegativity;
-- * ordinary unmasked cell charge <= physical dissipation.
--
-- The dyadic 1/2, recurrence induction, inverse-shell certificate and owner
-- eta = 2M are all derived internally.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedGainDensityRound39Exact as Gain
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedChargeSubchargeRound44Exact as Subcharge
import DASHI.Physics.Closure.NSTriadKNHHBadOneDerivativeFactorizationRound44Exact as Factor
import DASHI.Physics.Closure.NSTriadKNHHBadDefectRecurrenceNormalizationRound46Exact as Defect
import DASHI.Physics.Closure.NSTriadKNHHBadDyadicThreeMechanismRecurrenceRound48Exact as Three
import DASHI.Physics.Closure.NSTriadKNHHBadSelectedRecurrenceToOwnerRound47Exact as ToOwner
import DASHI.Physics.Closure.NSTriadKNHHBadSelectedClosureWitnessRound48Exact as Closure
import DASHI.Physics.Closure.NSTriadKNHHBadNormalizedProfileRound45Exact as Profile
import DASHI.Physics.Closure.NSTriadKNHHBadSingleThresholdSufficesRound47Exact as Selected

record PhysicalDyadicSelectedHHBadClosureInput
    (environment : Owner.TaxEnvironment)
    (effectiveViscosity : ℚ) : Set₁ where
  field
    transfer : Three.PhysicalDyadicThreeMechanismTransfer

    density : Nat → ℚ
    densityNonnegative : ∀ shell → 0ℚ ≤ density shell
    cells : ∀ shell →
      List (Gain.RestrictedGainDensityCell
        effectiveViscosity (density shell) shell)

    normalizedDensityIsNormalizedDefect : ∀ shell →
      Factor.scaleFreeDensityCoefficient (density shell) shell
      ≡ Defect.normalizedDefectProfile
          (Three.asSelectedThresholdDefectRecurrence transfer
            |> DASHI.Physics.Closure.NSTriadKNHHBadSelectedThresholdRecurrenceRound47Exact.asPhysicalDefectRecurrence)
          shell

    viscosityNonnegative : 0ℚ ≤ effectiveViscosity

    unmaskedChargeBelowPhysicalDissipation : ∀ shell →
      Subcharge.sumCellUnmaskedViscousCharge
        effectiveViscosity shell
        (Gain.cells
          (Factor.asRound39InverseShellCertificate
            (Profile.canonicalOneDerivativeDensityAtShell
              (Selected.selectedThresholdToRound45Profile
                (ToOwner.selectedRecurrenceToOwnerProfile densityBridge))
              shell)))
      ≤ Owner.dissipation environment

  densityBridge :
    ToOwner.SelectedRecurrenceLiteralDensityBridge
      effectiveViscosity
      (Three.asSelectedThresholdDefectRecurrence transfer)
  densityBridge = record
    { density = density
    ; densityNonnegative = densityNonnegative
    ; cells = cells
    ; normalizedDensityIsNormalizedDefect =
        normalizedDensityIsNormalizedDefect
    }

open PhysicalDyadicSelectedHHBadClosureInput public

asPhysicalSelectedRecurrenceOwnerInput :
  ∀ {environment effectiveViscosity} →
  (input : PhysicalDyadicSelectedHHBadClosureInput
    environment effectiveViscosity) →
  ToOwner.PhysicalSelectedRecurrenceHHBadOwnerInput
    environment effectiveViscosity
    (Three.asSelectedThresholdDefectRecurrence (transfer input))
asPhysicalSelectedRecurrenceOwnerInput input = record
  { densityBridge = densityBridge input
  ; viscosityNonnegative = viscosityNonnegative input
  ; unmaskedChargeBelowPhysicalDissipation =
      unmaskedChargeBelowPhysicalDissipation input
  }

physicalDyadicSelectedClosureWitness :
  ∀ {environment effectiveViscosity} →
  PhysicalDyadicSelectedHHBadClosureInput environment effectiveViscosity →
  Closure.SelectedHHBadClosureWitness environment effectiveViscosity
physicalDyadicSelectedClosureWitness input = record
  { recurrence =
      Three.asSelectedThresholdDefectRecurrence (transfer input)
  ; physicalOwnerInput = asPhysicalSelectedRecurrenceOwnerInput input
  }

physicalDyadicSelectedHHBadOwner :
  ∀ {environment effectiveViscosity} →
  PhysicalDyadicSelectedHHBadClosureInput environment effectiveViscosity →
  Nat → Owner.AdmissibleOwnerEstimate environment
physicalDyadicSelectedHHBadOwner input =
  Closure.selectedHHBadOwnerAtShell
    (physicalDyadicSelectedClosureWitness input)

hhBadThreeMechanismToMatureOwnerClosed : Bool
hhBadThreeMechanismToMatureOwnerClosed = true

physicalHHBadThreeMechanismProducerConstructed : Bool
physicalHHBadThreeMechanismProducerConstructed = false

hhBadThreeMechanismToMatureOwnerClosedIsTrue :
  hhBadThreeMechanismToMatureOwnerClosed ≡ true
hhBadThreeMechanismToMatureOwnerClosedIsTrue = refl

physicalHHBadThreeMechanismProducerConstructedIsFalse :
  physicalHHBadThreeMechanismProducerConstructed ≡ false
physicalHHBadThreeMechanismProducerConstructedIsFalse = refl
