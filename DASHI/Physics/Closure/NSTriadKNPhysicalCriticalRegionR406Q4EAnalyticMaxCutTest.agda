module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406Q4EAnalyticMaxCutTest where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406Q4EAnalyticMaxCutExact as Cut

normalFormPaid : Cut.q4eExactNormalFormClosed ≡ true
normalFormPaid = refl

preferred : Cut.q4ePreferredB7Route ≡ true
preferred = refl

ftcStillOpen : Cut.q4eOffDiagonalFluxFTCClosed ≡ false
ftcStillOpen = refl

gramStillOpen : Cut.q4eIntegratedGramBoundClosed ≡ false
gramStillOpen = refl

endpointStillOpen : Cut.q4eFluxEndpointBoundClosed ≡ false
endpointStillOpen = refl
