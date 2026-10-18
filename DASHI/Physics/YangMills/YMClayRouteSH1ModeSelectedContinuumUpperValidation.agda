{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayRouteSH1ModeSelectedContinuumUpperValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YMClayRouteSH1ModeSelectedContinuumUpperExact as Route

noArbitraryClusteringEnvelope :
  Route.arbitrarySpectrumClusteringEnvelopeRequired ≡ false
noArbitraryClusteringEnvelope = refl

noFastEnvelopeCalibration :
  Route.fastSpectrumEnvelopeCalibrationRequired ≡ false
noFastEnvelopeCalibration = refl

noSourceEnvelope :
  Route.sourceEnvelopeRequired ≡ false
noSourceEnvelope = refl

noSourceRootDistanceCarrier :
  Route.sourceRootDistanceCarrierRequired ≡ false
noSourceRootDistanceCarrier = refl

distanceTimeRemainsPhysical :
  Route.selectedDistanceTimeStillPhysical ≡ true
distanceTimeRemainsPhysical = refl

limitClosureRemainsRequired :
  Route.selectedLimitUpperClosureStillRequired ≡ true
limitClosureRemainsRequired = refl

promotionFailClosed :
  Route.clayPromotion ≡ false
promotionFailClosed = refl
