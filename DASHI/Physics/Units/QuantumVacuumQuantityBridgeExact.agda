module DASHI.Physics.Units.QuantumVacuumQuantityBridgeExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Edgar Buckingham.
-- Title: "On Physically Similar Systems; Illustrations of the Use of
-- Dimensional Equations".
-- Physical Review 4 (1914), 345--376.
-- DOI: 10.1103/PhysRev.4.345.
--
-- PURPOSE
-- Reuse the existing finite quantum-vacuum quantity wrappers while assigning
-- them one common mechanical-dimension semantics.  Energy and Work remain
-- distinct nominal types even though both map to M L^2 T^-2.  The historical
-- `averagePower` operation remains explicitly a multiplication proxy; this
-- bridge does not relabel it as a physical quotient.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.QuantumVacuum.PhysicalQuantities as Finite
import DASHI.Physics.Units.MechanicalDimensionExact as Dimension

finiteEnergyQuantity :
  Finite.Energy → Dimension.Quantity Nat Dimension.energyDimension
finiteEnergyQuantity value =
  Dimension.quantity (Finite.Energy.magnitude value)

finiteWorkQuantity :
  Finite.Work → Dimension.Quantity Nat Dimension.workDimension
finiteWorkQuantity value =
  Dimension.quantity (Finite.Work.magnitude value)

finitePowerQuantity :
  Finite.Power → Dimension.Quantity Nat Dimension.powerDimension
finitePowerQuantity value =
  Dimension.quantity (Finite.Power.magnitude value)

finiteTimeQuantity :
  Finite.Time → Dimension.Quantity Nat Dimension.timeDimension
finiteTimeQuantity value =
  Dimension.quantity (Finite.Time.magnitude value)

finiteLengthQuantity :
  Finite.Length → Dimension.Quantity Nat Dimension.lengthDimension
finiteLengthQuantity value =
  Dimension.quantity (Finite.Length.magnitude value)

finiteAreaQuantity :
  Finite.Area → Dimension.Quantity Nat Dimension.areaDimension
finiteAreaQuantity value =
  Dimension.quantity (Finite.Area.magnitude value)

finiteFrequencyQuantity :
  Finite.Frequency → Dimension.Quantity Nat Dimension.frequencyDimension
finiteFrequencyQuantity value =
  Dimension.quantity (Finite.Frequency.magnitude value)

energyAndWorkDimensionsAgree :
  Dimension.energyDimension ≡ Dimension.workDimension
energyAndWorkDimensionsAgree = refl

energyWorkRoundTripPreserved :
  (energy : Finite.Energy) →
  finiteEnergyQuantity
    (Finite.workToEnergy (Finite.energyToWork energy))
  ≡ finiteEnergyQuantity energy
energyWorkRoundTripPreserved (Finite.energy value) = refl

finiteQuantityWrappersReused : Bool
finiteQuantityWrappersReused = true

averagePowerRemainsAccountingProxy : Bool
averagePowerRemainsAccountingProxy = true

averagePowerQuotientLawProved : Bool
averagePowerQuotientLawProved = false

finiteQuantityWrappersReusedIsTrue :
  finiteQuantityWrappersReused ≡ true
finiteQuantityWrappersReusedIsTrue = refl

averagePowerRemainsAccountingProxyIsTrue :
  averagePowerRemainsAccountingProxy ≡ true
averagePowerRemainsAccountingProxyIsTrue = refl

averagePowerQuotientLawProvedIsFalse :
  averagePowerQuotientLawProved ≡ false
averagePowerQuotientLawProvedIsFalse = refl
