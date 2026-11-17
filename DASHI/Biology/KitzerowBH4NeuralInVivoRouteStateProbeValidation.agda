module DASHI.Biology.KitzerowBH4NeuralInVivoRouteStateProbeValidation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

import DASHI.Biology.KitzerowBH4NeuralInVivoRouteStateProbeExact as RouteState

routeAndStateMatterBeyondTotalPoolAmount :
  RouteState.totalTissueBiopterinSufficesForMonoamineOutput RouteState.canonicalNeuralRouteStateBoundary ≡ false
  × RouteState.intracellularAndExtracellularBH4AreMechanisticallyEquivalent RouteState.canonicalNeuralRouteStateBoundary ≡ false
routeAndStateMatterBeyondTotalPoolAmount = refl , refl

inVivoTHAndTPHResponsesArePaidButNotSimultaneousAllocation :
  RouteState.peripheralBH4CanActivateTHInVivo RouteState.canonicalNeuralRouteStateBoundary ≡ true
  × RouteState.peripheralBH4CanActivateTPHInVivo RouteState.canonicalNeuralRouteStateBoundary ≡ true
  × RouteState.sameObjectSimultaneousMultiBranchAllocationPaid RouteState.canonicalNeuralRouteStateBoundary ≡ false
inVivoTHAndTPHResponsesArePaidButNotSimultaneousAllocation = refl , (refl , refl)

routeStateEvidenceDoesNotCloseWholeAllocator :
  RouteState.routeStateEvidenceClosesWholeAllocator RouteState.canonicalNeuralRouteStateBoundary ≡ false
routeStateEvidenceDoesNotCloseWholeAllocator = refl
