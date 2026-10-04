module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406Q4EAnalyticMaxCutTest where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406Q4EAnalyticMaxCutExact as Cut

normalFormPaid : Cut.q4eExactNormalFormClosed ≡ true
normalFormPaid = refl

preferred : Cut.q4ePreferredB7Route ≡ true
preferred = refl

derivativeCompilerPaid :
  Cut.q4eOffDiagonalFluxDerivativeCompilerClosed ≡ true
derivativeCompilerPaid = refl

ftcCompilerPaid :
  Cut.q4eOffDiagonalFluxFTCClosedGivenOrdinaryScalarFTC ≡ true
ftcCompilerPaid = refl

twoAnalyticLeaves : Cut.q4eResearchLeavesReducedToTwoAnalyticBounds ≡ true
twoAnalyticLeaves = refl

gramStillOpen : Cut.q4eIntegratedGramBoundClosed ≡ false
gramStillOpen = refl

endpointStillOpen : Cut.q4eFluxEndpointBoundClosed ≡ false
endpointStillOpen = refl

noPlumbingRemaining : Cut.q4eRepresentationOrTemporalPlumbingRemaining ≡ false
noPlumbingRemaining = refl
