module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingLiteralCompanion20261007Test where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingLiteralCompanion20261007Exact as C

literalCompanionClosed : C.b4LiteralCoreCompanionMeaningClosed ≡ true
literalCompanionClosed = C.b4LiteralCoreCompanionMeaningClosedIsTrue

baselineBoundClosed : C.b4PrincipalBaselineYoungBoundClosed ≡ true
baselineBoundClosed = C.b4PrincipalBaselineYoungBoundClosedIsTrue

semanticStrictCompilerClosed : C.b4LiteralCompanionStrictSplitCompilerClosed ≡ true
semanticStrictCompilerClosed = C.b4LiteralCompanionStrictSplitCompilerClosedIsTrue

strictImprovementOpen : C.b4PrincipalStrictImprovementBelowOneClosed ≡ false
strictImprovementOpen = C.b4PrincipalStrictImprovementBelowOneClosedIsFalse

defectPaymentOpen : C.b4DefectPhysicalPaymentClosed ≡ false
defectPaymentOpen = C.b4DefectPhysicalPaymentClosedIsFalse
