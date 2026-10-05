module DASHI.Physics.Closure.NSClayFacingBPureAnalysisFrontier20261005Test where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSClayFacingBPureAnalysisFrontier20261005Exact as F

strictSplitCompiler : F.b4GenericStrictSplitCompilerClosed ≡ true
strictSplitCompiler = F.b4GenericStrictSplitCompilerClosedIsTrue

fixedQuarterNotRequired : F.b4FixedQuarterMarginRequired ≡ false
fixedQuarterNotRequired = F.b4FixedQuarterMarginRequiredIsFalse

quarterOptional : F.b4QuarterMarginOptionalCompilerClosed ≡ true
quarterOptional = F.b4QuarterMarginOptionalCompilerClosedIsTrue

localEDGone : F.bLocalEDIndependentLeaf ≡ false
localEDGone = F.bLocalEDIndependentLeafIsFalse

frontierOpen : F.pureAnalysisFrontierClosed ≡ false
frontierOpen = F.pureAnalysisFrontierClosedIsFalse
