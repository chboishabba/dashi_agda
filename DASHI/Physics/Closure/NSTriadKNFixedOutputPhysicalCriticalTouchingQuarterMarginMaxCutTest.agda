module DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalTouchingQuarterMarginMaxCutTest where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalTouchingQuarterMarginMaxCutExact as Q

quarterMarginCompilerClosed : Q.b4QuarterMarginCompilerClosed ≡ true
quarterMarginCompilerClosed = Q.b4QuarterMarginCompilerClosedIsTrue

quarterMarginStrict : Q.b4QuarterThetaStrictlyBelowOne ≡ true
quarterMarginStrict = Q.b4QuarterThetaStrictlyBelowOneIsTrue

attachmentStillOpen : Q.b4QuarterMarginPhysicalAttachmentClosedHere ≡ false
attachmentStillOpen = Q.b4QuarterMarginPhysicalAttachmentClosedHereIsFalse
