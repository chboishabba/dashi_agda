module DASHI.Chemistry.DrinkingWaterTapMetalObservationBidiExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.DrinkingWaterCorrosionMetalReleaseExact as Metal
import DASHI.Chemistry.DrinkingWaterDistributionResidualCorrosionBidiExact as Distribution
import DASHI.Core.EmpiricalContactReceipt as Contact

------------------------------------------------------------------------
-- TAP-METAL OBSERVATION BIDI WELD
--
-- Reuses the canonical empirical-contact rule: an observation is a projection
-- from hidden carrier structure.  Sampling may constrain the fibre, but does
-- not recover the complete upstream pipe / scale / release / hydraulic state.
------------------------------------------------------------------------

data TapSamplingProtocolKind : Set where
  firstDraw
  postStagnation
  flushed
  sequentialVolumeProfile
  randomDaytime
  compositeOrOther
  : TapSamplingProtocolKind

data MetalMeasurementFraction : Set where
  dissolvedFraction
  particulateFraction
  totalFraction
  operationallyDefinedFraction
  : MetalMeasurementFraction

record TapMetalSamplingState : Set where
  constructor tapMetalSamplingState
  field
    tapObservation : Distribution.DistributionTapObservation
    protocolKind : TapSamplingProtocolKind
    stagnationDurationReference : String
    flushDurationOrVolumeReference : String
    sampledVolumeReference : String
    faucetAeratorStateReference : String
    samplePreservationReference : String
    filtrationFractionationReference : String
    analyticalMethodReference : String
    detectionQuantificationLimitReference : String
    chainOfCustodyReference : String

open TapMetalSamplingState public

record TapMetalObservationReceipt : Set₁ where
  constructor tapMetalObservationReceipt
  field
    sampling : TapMetalSamplingState
    measurementFraction : MetalMeasurementFraction
    measuredMetal : Metal.MetalKind
    measuredValueReference : String
    measurementUncertaintyReference : String
    hiddenReleaseState : Metal.MetalReleaseState
    empiricalContact : Contact.EmpiricalContactReceipt

    contactDoesNotPromoteTruth :
      Contact.promotesTruth empiricalContact ≡ false

    samplingAndHiddenStateCommonTapReference : String
    observationProjectionReference : String
    replayReference : String
    externalAuthorityReference : String

open TapMetalObservationReceipt public

------------------------------------------------------------------------
-- Non-factorability / anti-promotion surface.
------------------------------------------------------------------------

record TapMetalObservationBoundary : Set where
  constructor tapMetalObservationBoundary
  field
    oneTapMetalMeasurementRecoversUniquePipeMaterial : Bool
    oneTapMetalMeasurementRecoversUniquePipeMaterialIsFalse :
      oneTapMetalMeasurementRecoversUniquePipeMaterial ≡ false

    oneTapMetalMeasurementRecoversUniqueReleaseMechanism : Bool
    oneTapMetalMeasurementRecoversUniqueReleaseMechanismIsFalse :
      oneTapMetalMeasurementRecoversUniqueReleaseMechanism ≡ false

    firstDrawEqualsFlushedObservationLanguage : Bool
    firstDrawEqualsFlushedObservationLanguageIsFalse :
      firstDrawEqualsFlushedObservationLanguage ≡ false

    oneSampleRecoversStagnationAndHydraulicHistory : Bool
    oneSampleRecoversStagnationAndHydraulicHistoryIsFalse :
      oneSampleRecoversStagnationAndHydraulicHistory ≡ false

    lowDissolvedMetalProvesLowParticulateAndTotalMetal : Bool
    lowDissolvedMetalProvesLowParticulateAndTotalMetalIsFalse :
      lowDissolvedMetalProvesLowParticulateAndTotalMetal ≡ false

    observationRequiresSamplingAndEmpiricalContactReceipts : Bool
    observationRequiresSamplingAndEmpiricalContactReceiptsIsTrue :
      observationRequiresSamplingAndEmpiricalContactReceipts ≡ true

canonicalTapMetalObservationBoundary : TapMetalObservationBoundary
canonicalTapMetalObservationBoundary =
  tapMetalObservationBoundary
    false refl false refl false refl false refl false refl true refl
