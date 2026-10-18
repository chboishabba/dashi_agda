module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseAtomisticConfigurationValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseAtomisticConfigurationExact as Config

boundary = Config.canonicalAdKAtomisticConfigurationBoundary

_ : Config.stableAtomIndexRetained boundary ≡ true
_ = refl

_ : Config.atomicIdentityRetained boundary ≡ true
_ = refl

_ : Config.threeDimensionalCoordinatesTypedAsSILength boundary ≡ true
_ = refl

_ : Config.atomicMassConventionExplicitlyAttributed boundary ≡ true
_ = refl

_ : Config.configurationDeterminesMechanicsContext boundary ≡ false
_ = refl

_ : Config.registryIdentityDeterminesAtomicMassConvention boundary ≡ false
_ = refl
