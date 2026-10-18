module DASHI.Physics.Closure.NSClayFacingBLocalEDCompilerMaxCut20261004Test where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSClayFacingBLocalEDCompilerMaxCut20261004Exact as Cut

localEDAllocationCompilerClosed :
  Cut.bLocalEDAllocationCompilerClosed ≡ true
localEDAllocationCompilerClosed = refl

localEDIndependentAnalyticLeafRemoved :
  Cut.bLocalEDIndependentAnalyticLeaf ≡ false
localEDIndependentAnalyticLeafRemoved = refl

compilerIntroducesEstimateFalse :
  Cut.bLocalEDCompilerIntroducesEstimate ≡ false
compilerIntroducesEstimateFalse = refl
