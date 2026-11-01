{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Epitaxy.HeteroepitaxyStrainDefectExact where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)

-- Source:
-- Hui Ye and Jinzhong Yu, "Germanium epitaxy on silicon",
-- Science and Technology of Advanced Materials 15 (2014) 024601,
-- DOI: 10.1088/1468-6996/15/2/024601.
--
-- The review emphasizes lattice mismatch, strain relaxation, surface energy,
-- growth temperature and misfit/threading dislocations in Ge/Si heteroepitaxy.

record EpitaxyState : Set where
  constructor epitaxyState
  field
    incomingFluxCode      : Nat
    substrateTemperature  : Nat
    mismatchCode          : Nat
    incorporatedCode      : Nat
    relaxedCode           : Nat
    threadingDefectCode   : Nat

open EpitaxyState public

-- Equal incoming flux and substrate temperature need not determine equal defect
-- density when mismatch/relaxation history differs.
epiA : EpitaxyState
epiA = epitaxyState 100 650 4 90 20 5

epiB : EpitaxyState
epiB = epitaxyState 100 650 8 90 45 18

sameIncomingFlux : incomingFluxCode epiA ≡ incomingFluxCode epiB
sameIncomingFlux = refl

sameSubstrateTemperature : substrateTemperature epiA ≡ substrateTemperature epiB
sameSubstrateTemperature = refl

data ⊥ : Set where

sameFluxTemperatureDoesNotDetermineDefects :
  threadingDefectCode epiA ≡ threadingDefectCode epiB → ⊥
sameFluxTemperatureDoesNotDetermineDefects ()

record IncorporatedPartition : Set where
  constructor incorporatedPartition
  field
    deposited : Nat
    incorporated : Nat
    rejectedOrDesorbed : Nat
    accounting : incorporated + rejectedOrDesorbed ≡ deposited

open IncorporatedPartition public

syntheticPartition : IncorporatedPartition
syntheticPartition = incorporatedPartition 100 90 10 refl

data EpitaxyResidual : Set where
  LatticeConstant : EpitaxyResidual
  SurfaceEnergy : EpitaxyResidual
  InterfaceEnergy : EpitaxyResidual
  StepDensity : EpitaxyResidual
  AdatomMobility : EpitaxyResidual
  CriticalThickness : EpitaxyResidual
  MisfitDislocationNucleation : EpitaxyResidual
  ThreadingDislocationPropagation : EpitaxyResidual
  CompositionProfile : EpitaxyResidual
  SelectiveGrowthChemistry : EpitaxyResidual
  ExactProductionCondition : EpitaxyResidual
