module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406HomogeneityBoundaryMaxCutTest where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406HomogeneityBoundaryMaxCutExact as Cut

universalEqualityRejected :
  Cut.b7UniversalDirectCompanionCovarianceEqualityAdmissible ≡ false
universalEqualityRejected = refl

quantitativeTransportRequired :
  Cut.b7RequiresDynamicOrQuantitativeTransport ≡ true
quantitativeTransportRequired = refl

quantitativeTransportStillOpen :
  Cut.b7DynamicOrQuantitativeTransportClosed ≡ false
quantitativeTransportStillOpen = refl
