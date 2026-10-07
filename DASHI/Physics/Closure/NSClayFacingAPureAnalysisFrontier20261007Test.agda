module DASHI.Physics.Closure.NSClayFacingAPureAnalysisFrontier20261007Test where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSClayFacingAPureAnalysisFrontier20261007Exact as A

aCompilersClosed : A.aCompilerStackClosed ≡ true
aCompilersClosed = A.aCompilerStackClosedIsTrue

aGenericAnalysisNotFrontier : A.aGenericAnalysisResearchFrontier ≡ false
aGenericAnalysisNotFrontier = A.aGenericAnalysisResearchFrontierIsFalse

aInternalFrontierOpen : A.aInternalFrontierClosed ≡ false
aInternalFrontierOpen = A.aInternalFrontierClosedIsFalse
