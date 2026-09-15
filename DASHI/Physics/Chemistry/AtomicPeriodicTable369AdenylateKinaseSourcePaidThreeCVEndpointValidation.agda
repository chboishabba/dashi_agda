module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSourcePaidThreeCVEndpointValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSourcePaidThreeCVEndpointExact as Subject

open Subject

openThetaOne : thetaOneDegrees openEndpoint ≡ 95
openThetaOne = refl

openThetaTwo : thetaTwoDegrees openEndpoint ≡ 61
openThetaTwo = refl

openDLn : dLnAngstrom openEndpoint ≡ 38
openDLn = refl

closedThetaOne : thetaOneDegrees closedEndpoint ≡ 68
closedThetaOne = refl

closedThetaTwo : thetaTwoDegrees closedEndpoint ≡ 28
closedThetaTwo = refl

closedDLn : dLnAngstrom closedEndpoint ≡ 20
closedDLn = refl

sourcePaidThreeCvEndpoints : sourcePaysAllThreeEndpointCoordinates ≡ true
sourcePaidThreeCvEndpoints = refl

notAPath : endpointTripleDeterminesTransitionPath ≡ false
notAPath = refl

notIntermediateTable : endpointTripleCreatesIntermediateStateTable ≡ false
notIntermediateTable = refl
