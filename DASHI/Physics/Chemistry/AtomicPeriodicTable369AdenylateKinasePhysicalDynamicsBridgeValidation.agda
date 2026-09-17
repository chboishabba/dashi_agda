module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePhysicalDynamicsBridgeValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePhysicalDynamicsBridgeExact as Dynamics

boundary = Dynamics.canonicalAdKPhysicalDynamicsBridgeBoundary

_ : Dynamics.atomElementLayerRetained boundary ≡ true
_ = refl

_ : Dynamics.molecularSpeciesLayerRetained boundary ≡ true
_ = refl

_ : Dynamics.threeDimensionalGeometryLayerRetained boundary ≡ true
_ = refl

_ : Dynamics.atomisticProcessLayerRetained boundary ≡ true
_ = refl

_ : Dynamics.collectiveVariableMapRetained boundary ≡ true
_ = refl

_ : Dynamics.adkStateKernelLayerRetained boundary ≡ true
_ = refl

_ : Dynamics.biasPotentialEqualsPhysicalFreeEnergy boundary ≡ false
_ = refl

_ : Dynamics.cvStateGraphRecoversCompleteAtomisticDynamics boundary ≡ false
_ = refl

_ : Dynamics.identifiersCreateAtomisticState boundary ≡ false
_ = refl

_ : Dynamics.unsourcedForceFieldParametersPromoted boundary ≡ false
_ = refl
