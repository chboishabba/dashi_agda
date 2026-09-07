{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Device.ElectrostaticMaxwellCrossPollinationExact where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Promotion.MaxwellExteriorCalculusAdapter as Maxwell

-- Semiconductor electrostatics reuses the existing Maxwell lane's separation
-- between potential/field structure, source current, and continuity.  It does
-- NOT identify a semiconductor scalar electrostatic potential with Maxwell's
-- gauge-potential one-form; this is an architecture-level cross-pollination.

record ElectrostaticCell : Set where
  constructor electrostaticCell
  field
    potentialCode       : Nat
    mobileChargeCode    : Nat
    fixedChargeCode     : Nat
    trappedChargeCode   : Nat
    displacementFluxCode : Nat

open ElectrostaticCell public

record ChargeBalance : Set where
  constructor chargeBalance
  field
    initialCharge : Nat
    injected      : Nat
    extracted     : Nat
    recombined    : Nat
    finalCharge   : Nat
    conservation  : initialCharge + injected ≡ finalCharge + (extracted + recombined)

open ChargeBalance public

syntheticChargeBalance : ChargeBalance
syntheticChargeBalance = chargeBalance 100 30 20 10 100 refl

record MaxwellArchitectureReuse : Set where
  constructor maxwellArchitectureReuse
  field
    sourceAdapter : Maxwell.MaxwellExteriorCalculusAdapter
    sourcePotentialCarrier : Maxwell.OneForm
    sourceCurrentCarrier   : Maxwell.ThreeForm
    potentialCarrierIsCanonical :
      sourcePotentialCarrier ≡ Maxwell.canonicalPotentialOneForm
    currentCarrierIsCanonical :
      sourceCurrentCarrier ≡ Maxwell.sourceCurrentThreeForm

open MaxwellArchitectureReuse public

canonicalMaxwellArchitectureReuse : MaxwellArchitectureReuse
canonicalMaxwellArchitectureReuse =
  maxwellArchitectureReuse
    Maxwell.canonicalMaxwellExteriorCalculusAdapter
    Maxwell.canonicalPotentialOneForm
    Maxwell.sourceCurrentThreeForm
    refl
    refl

-- Physics firewall: Maxwell's exterior-calculus carrier supplies reusable
-- potential/source/continuity architecture, but semiconductor electrostatics
-- still requires a material permittivity, charge-density producer, boundary
-- conditions, and a Poisson/Gauss constitutive realization.
data ElectrostaticResidual : Set where
  PermittivityProfile       : ElectrostaticResidual
  ChargeDensityProfile      : ElectrostaticResidual
  BoundaryCondition         : ElectrostaticResidual
  PoissonGaussRealization   : ElectrostaticResidual
  CarrierStatistics         : ElectrostaticResidual
  QuantumConfinement        : ElectrostaticResidual
  ExactDeviceGeometry       : ElectrostaticResidual
