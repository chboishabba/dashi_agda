module DASHI.Environment.LESImpactMechanicalDimensionBridgeExact where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Units.MechanicalDimensionExact as Dim

------------------------------------------------------------------------
-- DIMENSIONAL SPINE FOR IMPACT / HYDRODYNAMIC EXCHANGE
--
-- Reuses the repository's Buckingham-attributed MechanicalDimension owner.
-- These are dimension identities only; they do not manufacture numerical laws.
------------------------------------------------------------------------

forceDimension : Dim.MechanicalDimension
forceDimension = Dim.massDimension Dim.⊗ᴰ Dim.accelerationDimension

momentumDimension : Dim.MechanicalDimension
momentumDimension = Dim.massDimension Dim.⊗ᴰ Dim.velocityDimension

impulseDimension : Dim.MechanicalDimension
impulseDimension = forceDimension Dim.⊗ᴰ Dim.timeDimension

pressureAreaDimension : Dim.MechanicalDimension
pressureAreaDimension = Dim.pressureDimension Dim.⊗ᴰ Dim.areaDimension

forceVelocityDimension : Dim.MechanicalDimension
forceVelocityDimension = forceDimension Dim.⊗ᴰ Dim.velocityDimension

energyRateDimension : Dim.MechanicalDimension
energyRateDimension = Dim.energyDimension Dim.⊗ᴰ Dim.frequencyDimension

momentumIsMassVelocity :
  momentumDimension ≡ Dim.massDimension Dim.⊗ᴰ Dim.velocityDimension
momentumIsMassVelocity = refl

impulseIsMomentum : impulseDimension ≡ momentumDimension
impulseIsMomentum = refl

pressureTimesAreaIsForce : pressureAreaDimension ≡ forceDimension
pressureTimesAreaIsForce = refl

forceTimesVelocityIsPower : forceVelocityDimension ≡ Dim.powerDimension
forceTimesVelocityIsPower = refl

energyRateIsPower : energyRateDimension ≡ Dim.powerDimension
energyRateIsPower = refl

------------------------------------------------------------------------
-- Generic quantity constructors.  A numerical backend supplies multiplication.
------------------------------------------------------------------------

momentumQuantity :
  ∀ {Scalar} →
  (Scalar → Scalar → Scalar) →
  Dim.Quantity Scalar Dim.massDimension →
  Dim.Quantity Scalar Dim.velocityDimension →
  Dim.Quantity Scalar momentumDimension
momentumQuantity multiply = Dim.multiplyQuantity multiply

impulseQuantity :
  ∀ {Scalar} →
  (Scalar → Scalar → Scalar) →
  Dim.Quantity Scalar forceDimension →
  Dim.Quantity Scalar Dim.timeDimension →
  Dim.Quantity Scalar impulseDimension
impulseQuantity multiply = Dim.multiplyQuantity multiply

pressureForceQuantity :
  ∀ {Scalar} →
  (Scalar → Scalar → Scalar) →
  Dim.Quantity Scalar Dim.pressureDimension →
  Dim.Quantity Scalar Dim.areaDimension →
  Dim.Quantity Scalar pressureAreaDimension
pressureForceQuantity multiply = Dim.multiplyQuantity multiply

mechanicalPowerQuantity :
  ∀ {Scalar} →
  (Scalar → Scalar → Scalar) →
  Dim.Quantity Scalar forceDimension →
  Dim.Quantity Scalar Dim.velocityDimension →
  Dim.Quantity Scalar forceVelocityDimension
mechanicalPowerQuantity multiply = Dim.multiplyQuantity multiply
