module DASHI.Biology.Agriculture.AustralianRestorationTrajectoryDataSurfaceRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.AustralianRestorationTrajectoryDataSurfaceExact as T

doiPinned :
  T.liddicoatEtAl2022DOI ≡ "10.1016/j.jenvman.2022.114748"
doiPinned = refl

huntlyLowerAgePinned :
  T.minimumRehabilitationAge T.huntlyTrajectoryData ≡ 2
huntlyLowerAgePinned = refl

huntlyUpperAgePinned :
  T.maximumRehabilitationAge T.huntlyTrajectoryData ≡ 29
huntlyUpperAgePinned = refl

eneabbaLowerAgePinned :
  T.minimumRehabilitationAge T.eneabbaTrajectoryData ≡ 7
eneabbaLowerAgePinned = refl

eneabbaUpperAgePinned :
  T.maximumRehabilitationAge T.eneabbaTrajectoryData ≡ 38
eneabbaUpperAgePinned = refl

worsleyLowerAgePinned :
  T.minimumRehabilitationAge T.worsleyTrajectoryData ≡ 2
worsleyLowerAgePinned = refl

worsleyUpperAgePinned :
  T.maximumRehabilitationAge T.worsleyTrajectoryData ≡ 28
worsleyUpperAgePinned = refl

datasetReusable :
  T.depositedDatasetExplicitlyReusable
    T.canonicalTrajectoryDataBoundary ≡ true
datasetReusable = refl

chronosequenceNotLongitudinal :
  T.ageIndexedChronosequenceEqualsRepeatedSamePlotTrajectory
    T.canonicalTrajectoryDataBoundary ≡ false
chronosequenceNotLongitudinal = refl

microbiomeNotWholeState :
  T.microbiomeSimilarityTrajectoryEqualsWholeEcosystemTrajectory
    T.canonicalTrajectoryDataBoundary ≡ false
microbiomeNotWholeState = refl

modelPredictionNotObservedIncrement :
  T.modelPredictedRecoveryTimeEqualsObservedSuccessiveStateIncrement
    T.canonicalTrajectoryDataBoundary ≡ false
modelPredictionNotObservedIncrement = refl
