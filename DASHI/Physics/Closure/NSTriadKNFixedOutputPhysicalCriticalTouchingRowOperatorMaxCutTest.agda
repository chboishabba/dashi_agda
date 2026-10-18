module DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalTouchingRowOperatorMaxCutTest where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalTouchingRowOperatorMaxCutExact as Cut

rowOperatorCompilerClosed : Cut.b4LiteralRowOperatorCompilerClosed ≡ true
rowOperatorCompilerClosed = refl

sameObjectNoLongerLeaf : Cut.b4RowOperatorSameObjectLeafRemaining ≡ false
sameObjectNoLongerLeaf = refl

strictEstimateStillOpen : Cut.b4LiteralRowStrictEstimateClosedHere ≡ false
strictEstimateStillOpen = refl
