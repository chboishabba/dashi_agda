module DASHI.Physics.Foundations.BalabanSpatialC3StressMaxCutValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.YangMills.BalabanCMP109SpatialC3ActionExact as CMP109C3
import DASHI.Physics.Foundations.BalabanR144SpatialC3StressRestrictionExact as R144C3

-- RED-first contract for the physically aligned spatial C3 max-cut.

cmp109HasXYZCycleFixingTime : CMP109C3.cmp109Spatial123C3Recovered ≡ true
cmp109HasXYZCycleFixingTime = refl

old012CycleNotUsedAsLorentzSpatialXYZ : CMP109C3.cycle012IsLorentzSpatialXYZ ≡ false
old012CycleNotUsedAsLorentzSpatialXYZ = refl

r144UsesSameHypercubicGeneratorFamily : R144C3.r144C3RestrictedFromExistingB4Action ≡ true
r144UsesSameHypercubicGeneratorFamily = refl

r144SignedTensorSpatialC3ActionRecovered : R144C3.r144SpatialC3TensorActionRecovered ≡ true
r144SignedTensorSpatialC3ActionRecovered = refl

r144SourceToStressC3ReducedToExistingCovarianceWitness :
  R144C3.r144SpatialC3NeedsNoNewAmbientCarrier ≡ true
r144SourceToStressC3ReducedToExistingCovarianceWitness = refl
