module DASHI.Physics.CondensedMatter.MATBGQTMResolutionAwareForwardObserverValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.CondensedMatter.MATBGQTMResolutionAwareForwardObserverReceiptExact as R

resolution-aware-observer-executed : R.syntheticResolutionAwareSurfaceExecuted R.canonicalQTMResolutionAwareForwardObserverBoundary ≡ true
resolution-aware-observer-executed = refl

experimental-arrays-remain-absent : R.experimentalArraysUsed R.canonicalQTMResolutionAwareForwardObserverReceipt ≡ false
experimental-arrays-remain-absent = refl

absolute-scale-remains-uncalibrated : R.absoluteWABSampleCalibrated R.canonicalQTMResolutionAwareForwardObserverReceipt ≡ false
absolute-scale-remains-uncalibrated = refl

interacting-fit-remains-unpaid : R.experimentalFitPaid R.canonicalQTMResolutionAwareForwardObserverReceipt ≡ false
interacting-fit-remains-unpaid = refl
