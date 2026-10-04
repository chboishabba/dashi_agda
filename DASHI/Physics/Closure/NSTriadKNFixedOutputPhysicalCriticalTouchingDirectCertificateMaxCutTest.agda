module DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalTouchingDirectCertificateMaxCutTest where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalTouchingDirectCertificateMaxCutExact as Cut

sameObjectFieldEliminated : Cut.b4ArbitrarySignedOperatorAliasEliminated ≡ true
sameObjectFieldEliminated = refl

strictEstimateStillOpen : Cut.b4DirectStrictEstimateClosedHere ≡ false
strictEstimateStillOpen = refl
