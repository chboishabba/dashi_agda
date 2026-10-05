module DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalTouchingStrictSplitMaxCutTest where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalTouchingStrictSplitMaxCutExact as S

compilerClosed : S.b4StrictSplitCompilerClosed ≡ true
compilerClosed = S.b4StrictSplitCompilerClosedIsTrue

fixedQuarterRequired : S.b4StrictSplitRequiresQuarterMargin ≡ false
fixedQuarterRequired = S.b4StrictSplitRequiresQuarterMarginIsFalse

physicalSplitOpen : S.b4StrictSplitPhysicalAttachmentClosedHere ≡ false
physicalSplitOpen = S.b4StrictSplitPhysicalAttachmentClosedHereIsFalse
