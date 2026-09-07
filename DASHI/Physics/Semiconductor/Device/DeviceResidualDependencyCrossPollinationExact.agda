{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Device.DeviceResidualDependencyCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.ResidualObserverDependencyExact as Residual

------------------------------------------------------------------------
-- Direct instantiation of the repo-wide residual-dependency seam.
------------------------------------------------------------------------

data DeviceState : Set where
  nominal hiddenInterfaceCoupling : DeviceState

data DiagnosticAction : Set where
  sweepGateBias : DiagnosticAction

data DeviceIndex : Set where
  interfaceIndex electrostaticIndex mobilityIndex contactIndex : DeviceIndex

data DependencyCode : Set where
  lowCoupling highCoupling : DependencyCode

data CoarseElectrical : Set where
  sameCoarseIV : CoarseElectrical

data DeviceInfluence :
  DeviceState → DiagnosticAction → DeviceIndex → DeviceIndex → Set where
  interfaceToElectrostatic :
    DeviceInfluence hiddenInterfaceCoupling sweepGateBias
      interfaceIndex electrostaticIndex
  electrostaticToMobility :
    DeviceInfluence hiddenInterfaceCoupling sweepGateBias
      electrostaticIndex mobilityIndex

deviceDependencyCode : DeviceState → DiagnosticAction → DependencyCode
deviceDependencyCode nominal sweepGateBias = lowCoupling
deviceDependencyCode hiddenInterfaceCoupling sweepGateBias = highCoupling

deviceResidualDependency :
  Residual.ResidualDependencyObserver
    DeviceState DiagnosticAction DeviceIndex DependencyCode
deviceResidualDependency = record
  { Influences = DeviceInfluence
  ; dependencyCode = deviceDependencyCode
  }

coarseElectricalObserver : Observer.Observer DeviceState CoarseElectrical
coarseElectricalObserver nominal = sameCoarseIV
coarseElectricalObserver hiddenInterfaceCoupling = sameCoarseIV

hiddenDeviceDependency :
  Residual.HiddenResidualDependency
    deviceResidualDependency coarseElectricalObserver sweepGateBias
hiddenDeviceDependency =
  Residual.hiddenResidualDependency
    nominal
    hiddenInterfaceCoupling
    refl
    (λ ())

deviceDependencyStrictlyRefinesCoarseIV :
  Observer.StrictRefinement
    coarseElectricalObserver
    (Residual.refinedObservationAt
      deviceResidualDependency coarseElectricalObserver sweepGateBias)
deviceDependencyStrictlyRefinesCoarseIV =
  Residual.hiddenResidualDependencyGivesStrictRefinement hiddenDeviceDependency

coarseIVCannotReconstructDependency :
  Residual.DependencyCodeDescendsAt
    deviceResidualDependency coarseElectricalObserver sweepGateBias → ⊥
coarseIVCannotReconstructDependency =
  Residual.hiddenResidualDependencyBlocksDescent hiddenDeviceDependency

------------------------------------------------------------------------
-- Diagnostic routing: the same generic coupling-score type used elsewhere in
-- DASHI can rank finite residual entanglement.  It is not automatically a
-- covariance/Gram/spectral-independence certificate.
------------------------------------------------------------------------

data DiagnosticRoute : Set where
  inspectInterface inspectElectrostatics inspectMobility inspectContact : DiagnosticRoute

deviceCouplingScore : Residual.CouplingScore DeviceState DiagnosticRoute
deviceCouplingScore nominal inspectInterface = 0
deviceCouplingScore nominal inspectElectrostatics = 0
deviceCouplingScore nominal inspectMobility = 0
deviceCouplingScore nominal inspectContact = 0
deviceCouplingScore hiddenInterfaceCoupling inspectInterface = 1
deviceCouplingScore hiddenInterfaceCoupling inspectElectrostatics = 2
deviceCouplingScore hiddenInterfaceCoupling inspectMobility = 3
deviceCouplingScore hiddenInterfaceCoupling inspectContact = 1

interfaceNoWorseThanMobility :
  Residual.NoWorseCoupled
    deviceCouplingScore hiddenInterfaceCoupling inspectInterface inspectMobility
interfaceNoWorseThanMobility = s≤s z≤n

-- Firewall:
-- finite diagnostic coupling score != physical covariance or certified ASI.
