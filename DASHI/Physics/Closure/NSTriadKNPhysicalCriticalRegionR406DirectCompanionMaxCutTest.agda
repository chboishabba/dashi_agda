module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406DirectCompanionMaxCutTest where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406DirectCompanionMaxCutExact as Cut

b7AggregationReceipt : Cut.b7R406GlobalAggregationClosed ≡ true
b7AggregationReceipt = refl

b7LocalWeldStillOpen : Cut.b7PerOutputDirectCompanionCovarianceWeldClosed ≡ false
b7LocalWeldStillOpen = refl
