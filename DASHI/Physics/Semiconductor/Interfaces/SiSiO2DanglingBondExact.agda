{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Interfaces.SiSiO2DanglingBondExact where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)

-- Source:
-- "Native defects at the Si/SiO2 interface-amorphous silicon revisited",
-- Applications of Surface Science 22-23 (1985) 879-890,
-- DOI: 10.1016/0378-5963(85)90220-X.
--
-- This owner records interface-trap / dangling-bond bookkeeping only.  It does
-- not claim a complete atomistic defect model or a production passivation law.

record InterfaceState : Set where
  constructor interfaceState
  field
    danglingBondCode : Nat
    passivatedCode    : Nat
    activeTrapCode    : Nat
    chargedTrapCode   : Nat

open InterfaceState public

interfaceA : InterfaceState
interfaceA = interfaceState 100 70 30 12

interfaceB : InterfaceState
interfaceB = interfaceState 100 90 10 4

sameInitialDanglingBondCoordinate :
  danglingBondCode interfaceA ≡ danglingBondCode interfaceB
sameInitialDanglingBondCoordinate = refl

data ⊥ : Set where

sameInitialDefectCountDoesNotDetermineActiveTraps :
  activeTrapCode interfaceA ≡ activeTrapCode interfaceB → ⊥
sameInitialDefectCountDoesNotDetermineActiveTraps ()

record PassivationAccounting : Set where
  constructor passivationAccounting
  field
    initialDefects : Nat
    passivated     : Nat
    remaining      : Nat
    accounting     : passivated + remaining ≡ initialDefects

open PassivationAccounting public

syntheticPassivation : PassivationAccounting
syntheticPassivation = passivationAccounting 100 90 10 refl

data InterfaceResidual : Set where
  AtomicStructure : InterfaceResidual
  ChargeTransitionLevel : InterfaceResidual
  CaptureCrossSection : InterfaceResidual
  HydrogenChemicalPotential : InterfaceResidual
  PassivationKinetics : InterfaceResidual
  OxidationHistory : InterfaceResidual
  InterfaceStrain : InterfaceResidual
  DisorderDistribution : InterfaceResidual
  FixedCharge : InterfaceResidual
  ExactProcessCondition : InterfaceResidual
