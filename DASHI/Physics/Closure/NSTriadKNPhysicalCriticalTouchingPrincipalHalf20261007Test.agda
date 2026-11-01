module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingPrincipalHalf20261007Test where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingPrincipalHalf20261007Exact as H

sharpWorkClosed : H.b4SharpCoherentWorkYoungClosed ≡ true
sharpWorkClosed = H.b4SharpCoherentWorkYoungClosedIsTrue

principalHalfClosed : H.b4PrincipalHalfCompanionBoundClosed ≡ true
principalHalfClosed = H.b4PrincipalHalfCompanionBoundClosedIsTrue

principalEDZero : H.b4PrincipalNeedsEDRemainder ≡ false
principalEDZero = H.b4PrincipalNeedsEDRemainderIsFalse

remainingOnlyDefect : H.b4RemainingStrictMarginIsDefectBelowHalf ≡ true
remainingOnlyDefect = H.b4RemainingStrictMarginIsDefectBelowHalfIsTrue
