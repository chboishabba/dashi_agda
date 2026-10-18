module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingLiteralRowsMaxCutTest where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingLiteralRowsMaxCutExact as Cut

criticalRowsExtracted : Cut.b4CriticalTouchingLiteralRowsExtracted ≡ true
criticalRowsExtracted = refl

sameObjectClosed : Cut.b4CriticalTouchingRowsSameObjectClosed ≡ true
sameObjectClosed = refl

strictEstimateStillOpen : Cut.b4StrictThetaEstimateClosedHere ≡ false
strictEstimateStillOpen = refl
