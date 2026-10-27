module DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoKzCalibrationCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoPublishedARPESConstraintsExact as CoARPES

------------------------------------------------------------------------
-- PRODUCTIVE ARPES k_z CALIBRATION CROSS-POLLINATION
--
-- Methodology donor:
--   Yang et al., Nature Communications 16, 1442 (2025)
--   DOI 10.1038/s41467-025-56647-7
--   public source-data deposit: Figshare 25865749 (Igor format).
--
-- The CrSb study performs a broad photon-energy scan, observes periodic bulk
-- dispersion, fits an inner potential V0 ~ 17 eV, and only then converts photon
-- energy to k_z.  This is useful methodology for the Co1/4TaSe2 literal-observer
-- route because Sprague et al. publish 48/51/55 eV -> k_z assignments, while
-- our current repository has not independently reconstructed their final-state
-- calibration.
--
-- This module transfers the CALIBRATION OBLIGATION, not CrSb's V0, work
-- function, lattice constant, matrix elements or measured spectrum.
------------------------------------------------------------------------

record ThreeDARPESCalibrationDonor : Set where
  constructor three-d-arpes-calibration-donor
  field
    sourceDOI : String
    publicFigshareRecord : String
    sourceDataIgorFormat : Bool
    broadPhotonEnergyScanUsed : Bool
    periodicKzDispersionObserved : Bool
    innerPotentialFitUsed : Bool
    reportedInnerPotentialEV : Nat
    spinResolvedValidationUsed : Bool

open ThreeDARPESCalibrationDonor public

crSbCalibrationDonor : ThreeDARPESCalibrationDonor
crSbCalibrationDonor =
  three-d-arpes-calibration-donor
    "10.1038/s41467-025-56647-7"
    "10.6084/m9.figshare.25865749"
    true true true true 17 true

record CoKzCalibrationObligation : Set where
  constructor co-kz-calibration-obligation
  field
    sourcePhotonAssignmentsAlreadyPinned : Bool
    literalPhotonScanStillNeeded : Bool
    workFunctionOrEquivalentNeeded : Bool
    innerPotentialOrEquivalentNeeded : Bool
    emissionGeometryNeeded : Bool
    reciprocalPeriodicityCheckNeeded : Bool
    uncertaintyPropagationNeeded : Bool
    rawWaveAxisMetadataNeeded : Bool

open CoKzCalibrationObligation public

canonicalCoKzCalibrationObligation : CoKzCalibrationObligation
canonicalCoKzCalibrationObligation =
  co-kz-calibration-obligation
    true true true true true true true true

existingCoPublishedTargets : CoARPES.PublishedTargetStatus
existingCoPublishedTargets = CoARPES.canonicalPublishedTargetStatus

record KzCrossPollinationBoundary : Set where
  constructor kz-cross-pollination-boundary
  field
    crSbInnerPotentialTransferredToCo : Bool
    crSbPhotonEnergiesTransferredToCo : Bool
    crSbRawDataIsCoRawData : Bool
    sourcePhotonAssignmentEqualsIndependentCalibration : Bool
    freeElectronFinalStateModelIsExactManyBodyTruth : Bool
    crSbProtocolProvidesUsefulCalibrationArchitecture : Bool

canonicalKzCrossPollinationBoundary : KzCrossPollinationBoundary
canonicalKzCrossPollinationBoundary =
  kz-cross-pollination-boundary false false false false false true
