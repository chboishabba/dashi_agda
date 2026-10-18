module DASHI.Mathematics.NumberTheory.FiniteDivisorPowerSumValidation where

open import DASHI.Core.Prelude

import DASHI.Mathematics.NumberTheory.FiniteDivisorPowerSumExact as P
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Series

sigma3One : P.sigma3 1 ≡ 1
sigma3One = refl

sigma3Two : P.sigma3 2 ≡ 9
sigma3Two = refl

sigma3Three : P.sigma3 3 ≡ 28
sigma3Three = refl

sigma3Four : P.sigma3 4 ≡ 73
sigma3Four = refl

sigma3Five : P.sigma3 5 ≡ 126
sigma3Five = refl

sigma3Six : P.sigma3 6 ≡ 252
sigma3Six = refl

sigma5One : P.sigma5 1 ≡ 1
sigma5One = refl

sigma5Two : P.sigma5 2 ≡ 33
sigma5Two = refl

sigma5Three : P.sigma5 3 ≡ 244
sigma5Three = refl

sigma5Four : P.sigma5 4 ≡ 1057
sigma5Four = refl

sigma5Five : P.sigma5 5 ≡ 3126
sigma5Five = refl

sigma5Six : P.sigma5 6 ≡ 8052
sigma5Six = refl

kernelSigma3 :
  (n : Nat) ->
  Series.sigma3 P.canonicalDivisorPowerKernel n ≡ P.sigma3 n
kernelSigma3 n = refl

kernelSigma5 :
  (n : Nat) ->
  Series.sigma5 P.canonicalDivisorPowerKernel n ≡ P.sigma5 n
kernelSigma5 n = refl
