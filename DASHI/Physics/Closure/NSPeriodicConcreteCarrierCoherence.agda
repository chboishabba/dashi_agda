module DASHI.Physics.Closure.NSPeriodicConcreteCarrierCoherence where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Closure.NSPeriodicConcreteCarrier

------------------------------------------------------------------------
-- One machine-checked convention ledger for every executable/formal lane.
------------------------------------------------------------------------

record ConcreteCarrierConventionView : Set where
  field
    cutoffView : CutoffNorm
    fourierL2View : FourierL2Convention
    multiplierView : DyadicMultiplierConvention
    energyPartitionView : DyadicEnergyPartitionConvention
    packetView : PacketConvention
    sobolevView : SobolevConvention
    radiusView packetHalfWidthView twiceSobolevView : Nat

open ConcreteCarrierConventionView public

canonicalConventionView : ConcreteCarrierConventionView
canonicalConventionView = record
  { cutoffView = maximumCoordinateNorm
  ; fourierL2View = coefficientUnitaryL2
  ; multiplierView = rationalMaximumNormHat
  ; energyPartitionView = normalizedSquaredHatPartition
  ; packetView = threeShellPacket
  ; sobolevView = sevenHalvesSobolev
  ; radiusView = 8
  ; packetHalfWidthView = 1
  ; twiceSobolevView = 7
  }

record ConcreteCarrierCoherence
    (C : PeriodicConcreteCarrier)
    (V : ConcreteCarrierConventionView) : Set where
  field
    cutoffCoherent : cutoffView V ≡ cutoffNorm C
    fourierL2Coherent : fourierL2View V ≡ fourierL2 C
    multiplierCoherent : multiplierView V ≡ dyadicMultiplier C
    energyPartitionCoherent :
      energyPartitionView V ≡ dyadicEnergyPartition C
    packetCoherent : packetView V ≡ packetConvention C
    sobolevCoherent : sobolevView V ≡ sobolevConvention C
    radiusCoherent : radiusView V ≡ separationRadius C
    packetHalfWidthCoherent :
      packetHalfWidthView V ≡ packetHalfWidth C
    twiceSobolevCoherent :
      twiceSobolevView V ≡ twiceSobolevExponent C

open ConcreteCarrierCoherence public

periodicConcreteCarrierCoherent :
  ConcreteCarrierCoherence periodicConcreteCarrier canonicalConventionView
periodicConcreteCarrierCoherent = record
  { cutoffCoherent = refl
  ; fourierL2Coherent = refl
  ; multiplierCoherent = refl
  ; energyPartitionCoherent = refl
  ; packetCoherent = refl
  ; sobolevCoherent = refl
  ; radiusCoherent = refl
  ; packetHalfWidthCoherent = refl
  ; twiceSobolevCoherent = refl
  }
