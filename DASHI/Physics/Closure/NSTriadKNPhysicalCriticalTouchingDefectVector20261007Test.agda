module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingDefectVector20261007Test where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingDefectVector20261007Exact as V

defectVectorClosed : V.b4DefectOneVectorNormalFormClosed ≡ true
defectVectorClosed = V.b4DefectOneVectorNormalFormClosedIsTrue

noAbsoluteValue : V.b4DefectVectorNormalFormIntroducesAbsoluteValue ≡ false
noAbsoluteValue = V.b4DefectVectorNormalFormIntroducesAbsoluteValueIsFalse

sharpVectorEnvelope : V.b4DefectSharpVectorYoungClosed ≡ true
sharpVectorEnvelope = V.b4DefectSharpVectorYoungClosedIsTrue

physicalBudgetOpen : V.b4DefectPhysicalVectorBudgetClosed ≡ false
physicalBudgetOpen = V.b4DefectPhysicalVectorBudgetClosedIsFalse
