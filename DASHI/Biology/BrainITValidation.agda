module DASHI.Biology.BrainITValidation where

open import DASHI.Core.Prelude

import DASHI.Biology.BrainITSourceBoundaryExact as Source
import DASHI.Biology.BrainITFunctionalClusterTransferExact as Transfer
import DASHI.Biology.BrainITObservationPromotionBoundaryExact as Boundary
import DASHI.Biology.BrainITConnectomeFMRIWeldExact as Weld
import DASHI.Biology.BrainITConsumerRelativeExact as Consumer
import DASHI.Biology.BrainITTableReceiptsExact as Tables

brainITMaxCutPinsSourceBoundary :
  Source.arbitraryThoughtReadingSupported Source.canonicalBrainITSourceBoundary
  ≡ false
brainITMaxCutPinsSourceBoundary = refl

brainITMaxCutPinsRemoteBoundary :
  Source.remotePointAtPersonReadingSupported Source.canonicalBrainITSourceBoundary
  ≡ false
brainITMaxCutPinsRemoteBoundary = refl

brainITMaxCutPinsSharedClusterCount :
  Transfer.functionalClusterCount Transfer.canonicalBrainITArchitecture ≡ 128
brainITMaxCutPinsSharedClusterCount = refl

brainITMaxCutPinsOneHourTransfer :
  Transfer.sourceReportsComparablePerformance Transfer.brainITOneHourTransfer
  ≡ true
brainITMaxCutPinsOneHourTransfer = refl

brainITMaxCutPinsObservationFirewall :
  Boundary.reconstructionDoesNotRecoverMicroscopicState ≡ true
brainITMaxCutPinsObservationFirewall = refl

brainITMaxCutPinsThoughtPromotionFirewall :
  Boundary.viewedImageReconstructionDoesNotImplyArbitraryThoughtReading ≡ true
brainITMaxCutPinsThoughtPromotionFirewall = refl

------------------------------------------------------------------------
-- New source-bound quantitative and consumer-relative integration spine.
------------------------------------------------------------------------

brainITPinsPrimary15MinuteReport :
  Source.BrainITSourceBoundary.fifteenMinuteSubjectOneTransferIsPrimaryPaperClaim
    Source.canonicalBrainITSourceBoundary ≡ true
brainITPinsPrimary15MinuteReport = refl

brainITPins15MinuteSamples :
  Tables.transfer15minSamples Tables.canonicalBrainITPaperReceipt ≡ 450
brainITPins15MinuteSamples = refl

brainITPins15MinutePixelCorr :
  Tables.pixelCorrMilli Tables.subjectOne15min ≡ 336
brainITPins15MinutePixelCorr = Tables.published15minPixelCorr

brainITPinsPublishedClustering :
  Tables.pixelCorrMilli (Tables.clusteringRow Tables.functional) ≡ 386
brainITPinsPublishedClustering = Tables.functionalPixelCorrelationPaperValue

brainITPinsConnectomeWeld :
  Weld.brainITFunctionalClusterCount ≡ 128
brainITPinsConnectomeWeld = Weld.brainITFunctionalClusterCountIs128

brainITPinsReplayBoundary :
  Tables.metricsIndependentlyRecomputed Tables.canonicalBrainITPaperReceipt ≡ false
brainITPinsReplayBoundary = Tables.reportOnlyNoEvaluatorReplay

brainITPinsConsumerCollision :
  (decoder : DASHI.Biology.NeuralRepresentationLaplacianExact.CoarseRegionalObservation → Nat) →
  ((state : DASHI.Biology.NeuralRepresentationLaplacianExact.PopulationActivation) →
     DASHI.Biology.NeuralRepresentationLaplacianExact.laplacianVariation state ≡
     decoder (DASHI.Biology.NeuralRepresentationLaplacianExact.fmriLikeObservation state)) →
  ⊥
brainITPinsConsumerCollision = Consumer.noUniversalLaplacianDecoder
