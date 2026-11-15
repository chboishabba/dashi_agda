module DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoARPESObserverManifestExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoARPESWitnessGateExact as ARPES
import DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoKzCalibrationCrossPollinationExact as Kz

------------------------------------------------------------------------
-- RAW IGOR -> CALIBRATED OBSERVER MANIFEST
--
-- scripts/co_tase2_arpes_observer_from_ibw.py consumes literal Igor bytes only
-- when an explicit manifest assigns wave paths to spin channels, declares the
-- energy/momentum dimensions and unit/offset conversions, supplies an
-- uncertainty model and names the polarimeter-response treatment.
--
-- It produces exactly the calibrated_arpes.npz schema consumed by the existing
-- forward-fit program.  No channel identity, momentum scale, uncertainty or
-- polarimeter correction is guessed from file names or publication prose.
------------------------------------------------------------------------

record RawIgorObserverManifestContract : Set where
  constructor raw-igor-observer-manifest-contract
  field
    literalIbwBytesRequired : Bool
    perWaveSHA256Produced : Bool
    explicitSpinLabelRequired : Bool
    explicitEnergyDimensionRequired : Bool
    explicitMomentumDimensionRequired : Bool
    energyUnitAndOffsetRequired : Bool
    momentumUnitAndOffsetRequired : Bool
    uncertaintyModelRequired : Bool
    polarimeterResponseModelRequired : Bool
    calibratedSpinDeclarationRequired : Bool
    commonPhysicalAxesChecked : Bool
    forwardFitSchemaProduced : Bool

open RawIgorObserverManifestContract public

canonicalRawIgorObserverManifestContract : RawIgorObserverManifestContract
canonicalRawIgorObserverManifestContract =
  raw-igor-observer-manifest-contract
    true true true true true true true true true true true true

record ObserverManifestStatus : Set where
  constructor observer-manifest-status
  field
    calibratedObserverAssemblerImplemented : Bool
    syntheticAssemblerSelfTestImplemented : Bool
    literalUCFIbwPayloadPresent : Bool
    literalCalibrationManifestPresent : Bool
    literalCalibratedObserverReceiptExecuted : Bool

canonicalObserverManifestStatus : ObserverManifestStatus
canonicalObserverManifestStatus =
  observer-manifest-status true true false false false

existingARPESAcquisitionStatus : ARPES.CoARPESAcquisitionStatus
existingARPESAcquisitionStatus = ARPES.canonicalCoARPESAcquisitionStatus

existingKzCalibrationBoundary : Kz.KzCrossPollinationBoundary
existingKzCalibrationBoundary = Kz.canonicalKzCrossPollinationBoundary

record ObserverManifestPromotionBoundary : Set where
  constructor observer-manifest-promotion-boundary
  field
    decodedArrayImpliesSpinChannelIdentity : Bool
    fileNameImpliesSpinChannelIdentity : Bool
    publicationPhotonAssignmentImpliesRawAxisCalibration : Bool
    declaredPolarimeterModelImpliesCorrectPolarimeterModel : Bool
    syntheticAssemblerSelfTestImpliesObservedSpectrum : Bool
    literalSameObjectBytesAndCalibrationStillRequired : Bool

canonicalObserverManifestPromotionBoundary : ObserverManifestPromotionBoundary
canonicalObserverManifestPromotionBoundary =
  observer-manifest-promotion-boundary false false false false false true
