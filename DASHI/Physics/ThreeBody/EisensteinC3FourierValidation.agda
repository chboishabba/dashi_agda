module DASHI.Physics.ThreeBody.EisensteinC3FourierValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.EisensteinNineRingInterferenceExact as E
import DASHI.Physics.ThreeBody.EisensteinC3FourierExact as F

cyclicThreeCloses :
  F.cyclicPermute (F.cyclicPermute (F.cyclicPermute F.sampleState))
  ≡ F.sampleState
cyclicThreeCloses = F.cyclicPermuteThree F.sampleState

modeZeroInvariant :
  F.mode0 (F.cyclicPermute F.sampleState) ≡ F.mode0 F.sampleState
modeZeroInvariant = F.mode0CyclicInvariant F.sampleState

modeOnePhaseLaw :
  F.mode1 (F.cyclicPermute F.sampleState)
  ≡ E.multiply E.omega F.sampleStateMode1
modeOnePhaseLaw = F.mode1CyclicEigen F.sampleState

modeTwoPhaseLaw :
  F.mode2 (F.cyclicPermute F.sampleState)
  ≡ E.multiply E.omegaSquared F.sampleStateMode2
modeTwoPhaseLaw = F.mode2CyclicEigen F.sampleState
