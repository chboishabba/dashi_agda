module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406PositiveEndpointAmplitudeMaxCutTest where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406PositiveEndpointAmplitudeMaxCutExact as E

aggregationClosed : E.ePositiveOutputAggregationClosed ≡ true
aggregationClosed = E.ePositiveOutputAggregationClosedIsTrue

globalAmplitudeOpen : E.eGlobalAmplitudeSumProducerClosedHere ≡ false
globalAmplitudeOpen = E.eGlobalAmplitudeSumProducerClosedHereIsFalse
