{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Etch.SheathIonEnergySkeletonExact where

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)

-- Finite sheath/ion-energy accounting skeleton.  A real plasma sheath model
-- requires charge, potential, collisions, RF phase and distribution functions.
-- Here we only own the causal separation between sheath potential code and the
-- delivered ion-energy coordinate.

record SheathState : Set where
  constructor sheathState
  field
    sheathPotentialCode : Nat
    chargeCode : Nat
    collisionLossCode : Nat
    ionEnergyCode : Nat

open SheathState public

-- Synthetic ideal collisionless relation: ion energy code = charge * potential.
IdealCollisionlessSheath : SheathState → Set
IdealCollisionlessSheath x = ionEnergyCode x ≡ chargeCode x * sheathPotentialCode x

idealFixture : SheathState
idealFixture = sheathState 40 1 0 40

idealFixtureLaw : IdealCollisionlessSheath idealFixture
idealFixtureLaw = refl

-- Equal sheath potential need not imply equal delivered ion energy once charge
-- state and collisional losses differ.
stateA : SheathState
stateA = sheathState 40 1 0 40

stateB : SheathState
stateB = sheathState 40 2 20 60

samePotential : sheathPotentialCode stateA ≡ sheathPotentialCode stateB
samePotential = refl

data ⊥ : Set where

samePotentialDoesNotDetermineIonEnergy : ionEnergyCode stateA ≡ ionEnergyCode stateB → ⊥
samePotentialDoesNotDetermineIonEnergy ()

data SheathResidual : Set where
  RFPhaseDistribution : SheathResidual
  ElectronTemperature : SheathResidual
  IonMass : SheathResidual
  MeanFreePath : SheathResidual
  CollisionalSheathModel : SheathResidual
  IonEnergyDistributionFunction : SheathResidual
  IonAngularDistributionFunction : SheathResidual
