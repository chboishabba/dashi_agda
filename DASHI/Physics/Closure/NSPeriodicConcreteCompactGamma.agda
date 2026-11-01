module DASHI.Physics.Closure.NSPeriodicConcreteCompactGamma where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

open import DASHI.Physics.Closure.NSPeriodicConcreteDyadicPartition using (pow2)

------------------------------------------------------------------------
-- Literal shell-energy observables used by the finite runner.
--
-- Ratios are represented by numerator/denominator pairs, so no division or
-- positivity side condition is hidden in an executable definition.
------------------------------------------------------------------------

ShellEnergy : Set
ShellEnergy = Nat → Nat

pred : Nat → Nat
pred zero = zero
pred (suc n) = n

monus : Nat → Nat → Nat
monus n zero = n
monus zero (suc m) = zero
monus (suc n) (suc m) = monus n m

sumThrough : ShellEnergy → Nat → Nat
sumThrough energy zero = energy zero
sumThrough energy (suc n) = sumThrough energy n + energy (suc n)

packetEnergy : ShellEnergy → Nat → Nat
packetEnergy energy K =
  energy (pred K) + energy K + energy (suc K)

record ExactRatio : Set where
  constructor ratio
  field
    numerator denominator : Nat

open ExactRatio public

gammaRatio : ShellEnergy → Nat → ExactRatio
gammaRatio energy K = ratio (energy K) (packetEnergy energy K)

packetFraction : ShellEnergy → Nat → Nat → ExactRatio
packetFraction energy cutoff K =
  ratio (packetEnergy energy K) (sumThrough energy cutoff)

offPacketRatio : ShellEnergy → Nat → Nat → ExactRatio
offPacketRatio energy cutoff K =
  ratio
    (monus (sumThrough energy cutoff) (packetEnergy energy K))
    (sumThrough energy cutoff)

weightedFiveHalvesSquared : ShellEnergy → Nat → Nat
weightedFiveHalvesSquared energy j =
  pow2 (5 * j) * energy j

dyadicDissipation : ShellEnergy → Nat → Nat
dyadicDissipation energy cutoff = go cutoff
  where
  go : Nat → Nat
  go zero = energy zero
  go (suc j) = go j + pow2 (2 * suc j) * energy (suc j)
