module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406ProducerChoiceMaxCutTest where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406ProducerChoiceMaxCutExact as Cut

endpointNormalFormPaid : Cut.b7ExactEndpointNormalFormCompilerClosed ≡ true
endpointNormalFormPaid = refl

quarticAlternativeAvailable : Cut.b7QuarticGramEndpointCompilerAvailable ≡ true
quarticAlternativeAvailable = refl

directRouteStillOpen : Cut.b7DirectSignedQuinticRouteClosed ≡ false
directRouteStillOpen = refl

quarticRouteStillOpen : Cut.b7QuarticGramEndpointRouteClosed ≡ false
quarticRouteStillOpen = refl
