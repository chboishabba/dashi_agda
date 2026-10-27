module DASHI.Analysis.CollatzSyracuseSharpBarrierThresholdValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.CollatzSyracuseSharpBarrierThresholdExact as Sharp

sharpThresholdPaid :
  Sharp.SharpBarrierThresholdBoundary.sharpQuotientThresholdPaid
    Sharp.canonicalSharpBarrierThresholdBoundary
  ≡ 1
sharpThresholdPaid = refl

paradoxicalBoundPaid :
  Sharp.SharpBarrierThresholdBoundary.paradoxicalQuotientUpperBoundPaid
    Sharp.canonicalSharpBarrierThresholdBoundary
  ≡ 1
paradoxicalBoundPaid = refl

oldLeavesRecovered :
  Sharp.SharpBarrierThresholdBoundary.earlyCylinderThresholdsRecovered
    Sharp.canonicalSharpBarrierThresholdBoundary
  ≡ 1
oldLeavesRecovered = refl

universalEscapeStillOpen :
  Sharp.SharpBarrierThresholdBoundary.sharpThresholdCreatesUniversalEscape
    Sharp.canonicalSharpBarrierThresholdBoundary
  ≡ 0
universalEscapeStillOpen = refl
