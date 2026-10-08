module DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoARPESWitnessGateExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Physics.CondensedMatter.ARPESBandFoldingWitnessGateExact as ARPES
import DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoPhysicalSymmetryExact as Physical

------------------------------------------------------------------------
-- CO1/4TASE2 -> GENERIC ARPES WITNESS GATE
--
-- Sprague et al. deposit the minimal raw ARPES dataset needed to replicate the
-- paper at UCF STARS dataset 30.  The dataset page is public and states that
-- the payload is Igor binary waves.  As of the 2026-10-08 acquisition attempt
-- from this execution environment, the native payload endpoint returns HTTP
-- 403, so no intensity array is invented and no exact observed spectral
-- witness is promoted.
------------------------------------------------------------------------

record CoARPESAcquisitionStatus : Set where
  constructor co-arpes-acquisition-status
  field
    sourceDOI : String
    datasetLandingPage : String
    sourceStatesRawARPESDeposited : Bool
    sourceStatesMinimalReplicationDataset : Bool
    payloadFormatIgorBinaryWave : Bool
    nativePayloadAcquiredInRepository : Bool
    calibratedAxesConstructed : Bool
    spinResolvedIntensityArrayConstructed : Bool
    exactSpectralObserverConstructed : Bool
    quantitativeExperimentalFitClosed : Bool

open CoARPESAcquisitionStatus public

canonicalCoARPESAcquisitionStatus : CoARPESAcquisitionStatus
canonicalCoARPESAcquisitionStatus =
  co-arpes-acquisition-status
    "10.1038/s41467-026-76784-x"
    "https://stars.library.ucf.edu/datasets/30/"
    true true true
    false false false false false

-- Reuse, rather than duplicate, the repository-wide ARPES epistemic boundary.
existingARPESPromotionBoundary : ARPES.WitnessPromotionBoundary
existingARPESPromotionBoundary = ARPES.canonicalWitnessPromotionBoundary

record CoARPESFitObligations : Set where
  constructor co-arpes-fit-obligations
  field
    rawWaveIntegrityHash : Bool
    energyAxisCalibration : Bool
    parallelMomentumCalibration : Bool
    kzPhotonEnergyCalibration : Bool
    polarizationOrSpinChannelMetadata : Bool
    peakExtractionWithUncertainty : Bool
    forwardSpectralModel : Bool
    heldOutResidualReceipt : Bool

canonicalCoARPESFitObligations : CoARPESFitObligations
canonicalCoARPESFitObligations =
  co-arpes-fit-obligations false false false false false false false false

-- Existing sourced k-space assignments remain usable as source claims, but do
-- not become measured intensity arrays.
existing48eVAssignment :
  Physical.experimentalKzAssignment Physical.eV48 ≡ Physical.zeroPlane
existing48eVAssignment = refl

existing55eVAssignment :
  Physical.experimentalKzAssignment Physical.eV55 ≡ Physical.positiveHalf
existing55eVAssignment = refl
