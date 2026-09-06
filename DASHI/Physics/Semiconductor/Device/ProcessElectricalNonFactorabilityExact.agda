{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Device.ProcessElectricalNonFactorabilityExact where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Physics.Semiconductor.Doping.ImplantDiffusionAnnealExact as Doping
import DASHI.Physics.Semiconductor.Interfaces.SiSiO2DanglingBondExact as Interface

record DeviceProcessState : Set where
  constructor deviceProcessState
  field
    annealState       : Doping.AnnealState
    interfaceState    : Interface.InterfaceState
    geometryCode      : Nat
    thresholdCode     : Nat
    driveCurrentCode  : Nat

open DeviceProcessState public

record CoarseProcessProjection : Set where
  constructor coarseProcessProjection
  field
    activeDopantCode : Nat
    printedGeometryCode : Nat

open CoarseProcessProjection public

coarseProjection : DeviceProcessState → CoarseProcessProjection
coarseProjection x =
  coarseProcessProjection
    (Doping.activeAfter (annealState x))
    (geometryCode x)

thresholdObservable : DeviceProcessState → Nat
thresholdObservable = thresholdCode

-- Same activated dopant count and same coarse geometry, but different interface
-- trap state, can yield different electrical observables in the synthetic
-- finite carrier.
deviceA : DeviceProcessState
deviceA =
  deviceProcessState
    Doping.annealA
    Interface.interfaceA
    20
    40
    100

deviceB : DeviceProcessState
deviceB =
  deviceProcessState
    Doping.annealA
    Interface.interfaceB
    20
    55
    80

sameCoarseProcessProjection : coarseProjection deviceA ≡ coarseProjection deviceB
sameCoarseProcessProjection = refl

thresholdsDiffer : thresholdObservable deviceA ≡ thresholdObservable deviceB → ⊥
thresholdsDiffer ()

processElectricalNonFactorability :
  NF.NonFactorabilityWitness coarseProjection thresholdObservable
processElectricalNonFactorability =
  NF.nonFactorabilityWitness
    deviceA
    deviceB
    sameCoarseProcessProjection
    thresholdsDiffer

coarseProcessCannotDetermineThreshold :
  NF.FactorsThrough coarseProjection thresholdObservable → ⊥
coarseProcessCannotDetermineThreshold =
  NF.witnessRulesOutEveryFlatFactorisation
    processElectricalNonFactorability

-- This is the repository-wide nonfactorability theorem reused directly in a
-- physical process/device setting.  A coarse process monitor cannot recover an
-- electrical variable that depends on hidden interface/device state once the
-- projection has erased that distinction.
