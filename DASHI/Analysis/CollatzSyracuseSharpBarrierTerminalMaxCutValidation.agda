module DASHI.Analysis.CollatzSyracuseSharpBarrierTerminalMaxCutValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.CollatzSyracuseSharpBarrierTerminalMaxCutExact as MaxCut

sharpThresholdPaid :
  MaxCut.SharpBarrierTerminalBoundary.sharpThresholdAndMinimalityPaid
    MaxCut.canonicalSharpBarrierTerminalBoundary
  ≡ 1
sharpThresholdPaid = refl

coefficientBoundaryPaid :
  MaxCut.SharpBarrierTerminalBoundary.coefficientStoppingInternalBoundaryPaid
    MaxCut.canonicalSharpBarrierTerminalBoundary
  ≡ 1
coefficientBoundaryPaid = refl

oneZeroPaid :
  MaxCut.SharpBarrierTerminalBoundary.trailingOneZeroBarrierLawPaid
    MaxCut.canonicalSharpBarrierTerminalBoundary
  ≡ 1
oneZeroPaid = refl

universalEscapeOpen :
  MaxCut.SharpBarrierTerminalBoundary.universalCorrectionEscapeProducerPaid
    MaxCut.canonicalSharpBarrierTerminalBoundary
  ≡ 0
universalEscapeOpen = refl

universalCSTOpen :
  MaxCut.SharpBarrierTerminalBoundary.universalCoefficientStoppingEqualityPaid
    MaxCut.canonicalSharpBarrierTerminalBoundary
  ≡ 0
universalCSTOpen = refl
