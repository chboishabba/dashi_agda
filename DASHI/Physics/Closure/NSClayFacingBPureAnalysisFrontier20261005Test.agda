module DASHI.Physics.Closure.NSClayFacingBPureAnalysisFrontier20261005Test where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSClayFacingBPureAnalysisFrontier20261005Exact as F

quarterCompiler : F.b4QuarterMarginCompilerClosed ≡ true
quarterCompiler = F.b4QuarterMarginCompilerClosedIsTrue

quarterStrict : F.b4QuarterThetaStrictlyBelowOne ≡ true
quarterStrict = F.b4QuarterThetaStrictlyBelowOneIsTrue

localEDGone : F.bLocalEDIndependentLeaf ≡ false
localEDGone = F.bLocalEDIndependentLeafIsFalse

frontierOpen : F.pureAnalysisFrontierClosed ≡ false
frontierOpen = F.pureAnalysisFrontierClosedIsFalse
