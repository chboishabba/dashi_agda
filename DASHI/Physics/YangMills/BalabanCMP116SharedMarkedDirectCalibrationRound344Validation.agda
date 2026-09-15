{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SharedMarkedDirectCalibrationRound344Validation where

-- RED regression for the actual shared CMP116 marked carrier.

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.YangMills.BalabanCMP116SharedMarkedDirectCalibrationRound344Exact as R344

genericExponentialRepackagingNotMandatory :
  R344.genericExponentialShellRepackagingMandatory ≡ false
genericExponentialRepackagingNotMandatory =
  R344.genericExponentialShellRepackagingMandatoryIsFalse

sharedMarkedProducerBuildsR342 :
  R344.sharedMarkedDirectBuildsR342Source ≡ true
sharedMarkedProducerBuildsR342 =
  R344.sharedMarkedDirectBuildsR342SourceIsTrue

liveCoordinatesAreLocalizationDistanceConstant :
  R344.onlyLocalizationDistanceConstantRemain ≡ true
liveCoordinatesAreLocalizationDistanceConstant =
  R344.onlyLocalizationDistanceConstantRemainIsTrue
