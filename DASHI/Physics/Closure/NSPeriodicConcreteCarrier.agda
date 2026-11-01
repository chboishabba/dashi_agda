module DASHI.Physics.Closure.NSPeriodicConcreteCarrier where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Closure.NSIntegerFourierLattice using (FourierMode)

------------------------------------------------------------------------
-- Frozen conventions shared by the exact finite operators, numerical Galerkin
-- diagnostics and analytic bridge.
------------------------------------------------------------------------

data CutoffNorm : Set where
  maximumCoordinateNorm : CutoffNorm

data FourierL2Convention : Set where
  coefficientUnitaryL2 : FourierL2Convention

data DyadicMultiplierConvention : Set where
  rationalMaximumNormHat : DyadicMultiplierConvention

data DyadicEnergyPartitionConvention : Set where
  normalizedSquaredHatPartition : DyadicEnergyPartitionConvention

data PacketConvention : Set where
  threeShellPacket : PacketConvention

data SobolevConvention : Set where
  sevenHalvesSobolev : SobolevConvention

record PeriodicConcreteCarrier : Set₁ where
  field
    Mode : Set
    cutoffNorm : CutoffNorm
    fourierL2 : FourierL2Convention
    dyadicMultiplier : DyadicMultiplierConvention
    dyadicEnergyPartition : DyadicEnergyPartitionConvention
    packetConvention : PacketConvention
    sobolevConvention : SobolevConvention

    separationRadius : Nat
    packetHalfWidth : Nat
    twiceSobolevExponent : Nat

open PeriodicConcreteCarrier public

periodicConcreteCarrier : PeriodicConcreteCarrier
periodicConcreteCarrier = record
  { Mode = FourierMode
  ; cutoffNorm = maximumCoordinateNorm
  ; fourierL2 = coefficientUnitaryL2
  ; dyadicMultiplier = rationalMaximumNormHat
  ; dyadicEnergyPartition = normalizedSquaredHatPartition
  ; packetConvention = threeShellPacket
  ; sobolevConvention = sevenHalvesSobolev
  ; separationRadius = 8
  ; packetHalfWidth = 1
  ; twiceSobolevExponent = 7
  }

radiusIsEight : separationRadius periodicConcreteCarrier ≡ 8
radiusIsEight = refl

packetHasHalfWidthOne : packetHalfWidth periodicConcreteCarrier ≡ 1
packetHasHalfWidthOne = refl

sobolevExponentIsSevenHalves :
  twiceSobolevExponent periodicConcreteCarrier ≡ 7
sobolevExponentIsSevenHalves = refl

energyPartitionUsesNormalizedHatSquares :
  dyadicEnergyPartition periodicConcreteCarrier ≡
  normalizedSquaredHatPartition
energyPartitionUsesNormalizedHatSquares = refl

concreteCarrierSuppliesUniversalAnalyticTheorems : Bool
concreteCarrierSuppliesUniversalAnalyticTheorems = false
