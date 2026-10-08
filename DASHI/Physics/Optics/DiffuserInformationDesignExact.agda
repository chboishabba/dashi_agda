module DASHI.Physics.Optics.DiffuserInformationDesignExact where

-- Information/risk design layer for diffraction-coded imaging.
-- The optimisation target is attached to one concrete detector channel and one
-- declared scene/consumer family.  No objective value is promoted to universal
-- optical superiority, and no output-alphabet bit count becomes voxel accuracy.

open import Agda.Primitive using (Set; Set₁)
open import Relation.Binary.PropositionalEquality using (_≡_)

import DASHI.Physics.Optics.PhotonDetectorChannelExact as Detector
import DASHI.Foundations.HyperformObserverFactorisationExact as Observer

record ImagingDesignObjective
    (Design Scene ExpectedCounts Charge PixelData Recorded ConsumerOutcome Score : Set)
    (channelFor : Design →
      Detector.PhotonDetectorChannel Scene ExpectedCounts Charge PixelData Recorded)
    : Set₁ where
  field
    selectedDesign : Design
    physicalChannel :
      Detector.PhotonDetectorChannel Scene ExpectedCounts Charge PixelData Recorded

    samePhysicalChannel :
      physicalChannel ≡ channelFor selectedDesign

    consumer : Scene → ConsumerOutcome
    estimator : Recorded → ConsumerOutcome

    consumerRisk : Design → Score
    mutualInformationObjective : Design → Score

    sceneFamilyAuthority : Set
    sceneFamilyReceipt : sceneFamilyAuthority
    priorOrMinimaxAuthority : Set
    priorOrMinimaxReceipt : priorOrMinimaxAuthority
    objectiveCalibrationAuthority : Set
    objectiveCalibrationReceipt : objectiveCalibrationAuthority

open ImagingDesignObjective public

record DesignComparisonReceipt
    {Design Scene ExpectedCounts Charge PixelData Recorded ConsumerOutcome Score : Set}
    {channelFor : Design →
      Detector.PhotonDetectorChannel Scene ExpectedCounts Charge PixelData Recorded}
    (O : ImagingDesignObjective
      Design Scene ExpectedCounts Charge PixelData Recorded ConsumerOutcome Score channelFor)
    : Set₁ where
  field
    candidate : Design
    candidateScore : Score
    selectedScore : Score
    comparisonAuthority : Set
    comparisonReceipt : comparisonAuthority

open DesignComparisonReceipt public

-- Cross-pollination point: consumer adequacy remains observer-relative.
-- This module imports the canonical observer-fibre machinery rather than
-- replacing it with an information-theory-only notion of sufficiency.
