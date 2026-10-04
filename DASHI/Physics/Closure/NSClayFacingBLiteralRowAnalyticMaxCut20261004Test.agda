module DASHI.Physics.Closure.NSClayFacingBLiteralRowAnalyticMaxCut20261004Test where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSClayFacingBLiteralRowAnalyticMaxCut20261004Exact as Cut

literalRowCompilerClosed : Cut.bLiteralRowAnalyticCompilerClosed ≡ true
literalRowCompilerClosed = refl

legacyReceiptFrontierRemoved : Cut.bLegacyReceiptFrontierStillRequired ≡ false
legacyReceiptFrontierRemoved = refl

localEDIndependentLeafRemoved : Cut.bLocalEDIndependentLeafRemaining ≡ false
localEDIndependentLeafRemoved = refl

analyticRowEstimatesStillOpen : Cut.bLiteralRowAnalyticEstimatesClosedHere ≡ false
analyticRowEstimatesStillOpen = refl
