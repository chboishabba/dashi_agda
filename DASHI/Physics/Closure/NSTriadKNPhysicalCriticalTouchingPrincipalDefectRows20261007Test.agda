module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingPrincipalDefectRows20261007Test where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingPrincipalDefectRows20261007Exact as S

splitClosed : S.b4LiteralPrincipalDefectSplitClosed ≡ true
splitClosed = S.b4LiteralPrincipalDefectSplitClosedIsTrue

liveBlockWeldClosed : S.b4PrincipalDefectLiveBlockWeldClosed ≡ true
liveBlockWeldClosed = S.b4PrincipalDefectLiveBlockWeldClosedIsTrue

principalEstimateOpen : S.b4PrincipalPhysicalEstimateClosedHere ≡ false
principalEstimateOpen = S.b4PrincipalPhysicalEstimateClosedHereIsFalse

defectEstimateOpen : S.b4DefectPhysicalEstimateClosedHere ≡ false
defectEstimateOpen = S.b4DefectPhysicalEstimateClosedHereIsFalse
