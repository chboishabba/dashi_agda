{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.EUVSource.SourcePowerMilestonesExact where

open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)

-- Public ASML milestone coordinates.  These are historical/product-level
-- source-output coordinates, not decompositions of the proprietary source
-- recipe that realizes them.

prototypeSourcePowerW : Nat
prototypeSourcePowerW = 1

hvmSourcePower2018W : Nat
hvmSourcePower2018W = 250

prototypeSourcePower2022W : Nat
prototypeSourcePower2022W = 500

demonstrationSourcePower2025W : Nat
demonstrationSourcePower2025W = 1000

latestCommercialRepeatRateHz : Nat
latestCommercialRepeatRateHz = 60000

demonstrationRepeatRateHz : Nat
demonstrationRepeatRateHz = 100000

-- The publicly described repeat-rate step from 60 kHz to 100 kHz has exact
-- ratio 5/3.  This theorem is only about event rate; it does not assert that
-- optical power must scale linearly with repeat rate.
repeatRateRatioWitness :
  5 * latestCommercialRepeatRateHz ≡ 3 * demonstrationRepeatRateHz
repeatRateRatioWitness = refl

-- Likewise, the public 500 W -> 1000 W milestone is an exact factor-two output
-- coordinate, but no theorem here assigns that gain to any one underlying
-- engineering change.
prototypeToDemoPowerDoubling :
  2 * prototypeSourcePower2022W ≡ demonstrationSourcePower2025W
prototypeToDemoPowerDoubling = refl
