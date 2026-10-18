{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLevel2D3ConservedWardChargeValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.YangMills.YMClayLevel2D3ConservedWardChargeExact as D3
import DASHI.Physics.YangMills.YMClayLevel2ContinuumWardTransportExact as Transport

finiteTimeConservationIsDerived :
  D3.independentFiniteTimeChargeConservationRequiredInD3 ≡ false
finiteTimeConservationIsDerived =
  D3.independentFiniteTimeChargeConservationRequiredInD3IsFalse

cutoffTransportRemains :
  D3.cutoffToContinuumConservedChargeTransportStillPhysical ≡ true
cutoffTransportRemains =
  D3.cutoffToContinuumConservedChargeTransportStillPhysicalIsTrue

transportOwnerDoesNotRechargeFiniteConservation :
  Transport.independentFiniteTimeChargeConservationRequired ≡ false
transportOwnerDoesNotRechargeFiniteConservation =
  Transport.independentFiniteTimeChargeConservationRequiredIsFalse
