module DASHI.Biology.KitzerowBH4NeuralRouteStateAcquisitionStatusExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.KitzerowBH4NeuralInVivoRouteStateProbeExact as RouteState

record NeuralRouteStateAcquisitionStatus : Set where
  constructor neuralRouteStateAcquisitionStatus
  field
    routeStateCoordinatePaid : Bool
    routeStateCoordinatePaidIsTrue : routeStateCoordinatePaid ≡ true
    simultaneousAllocationCoordinatePaid : Bool
    simultaneousAllocationCoordinatePaidIsFalse : simultaneousAllocationCoordinatePaid ≡ false
    paidReference : String
    remainingReference : String
    wholeAllocatorClosed : Bool
    wholeAllocatorClosedIsFalse : wholeAllocatorClosed ≡ false

open NeuralRouteStateAcquisitionStatus public

canonicalNeuralRouteStateAcquisitionStatus : NeuralRouteStateAcquisitionStatus
canonicalNeuralRouteStateAcquisitionStatus =
  neuralRouteStateAcquisitionStatus
    true refl
    false refl
    "Nakahara 1988 + Koshimura/Miwa/Watanabe 1994 + Nagatsu et al. 1994 + Ishida et al. 1998 pay that total tissue BH4, intracellular cofactor state, extracellular BH4 exposure and branch response are distinct coordinates; peripheral BH4 can activate TH and TPH in vivo in source-specific contexts"
    "one target-neural donor-labelled BH4/BH2 experiment joining transfer rate/direction to simultaneous TH/TPH/NOS/AGMO branch mediation, NAD(P)H/redox and enzyme/transporter state remains unpaid"
    false refl

routeStatePaymentDoesNotCloseAllocator :
  RouteState.routeStateEvidenceClosesWholeAllocator RouteState.canonicalNeuralRouteStateBoundary ≡ false
routeStatePaymentDoesNotCloseAllocator = refl
