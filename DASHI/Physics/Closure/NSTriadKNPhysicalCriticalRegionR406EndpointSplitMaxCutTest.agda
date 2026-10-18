module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406EndpointSplitMaxCutTest where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406EndpointSplitMaxCutExact as Cut

endpointSplitCompilerClosed : Cut.q4eEndpointIncrementSplitCompilerClosed ≡ true
endpointSplitCompilerClosed = refl

negativeOrientationProducerExists : Cut.q4eNegativeEndpointOrientationProducerExists ≡ true
negativeOrientationProducerExists = refl

positiveTerminalStillOpen : Cut.q4ePositiveTerminalFluxUniformBoundClosedHere ≡ false
positiveTerminalStillOpen = refl
