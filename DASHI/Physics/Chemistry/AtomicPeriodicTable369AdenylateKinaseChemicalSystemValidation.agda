module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseChemicalSystemValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseChemicalSystemExact as Chemical

boundary = Chemical.canonicalAdKChemicalSystemBoundary

_ : Chemical.reusesCanonicalChemistryKernel boundary ≡ true
_ = refl

_ : Chemical.reusesAtomicToMolecularHyperformalism boundary ≡ true
_ = refl

_ : Chemical.atpAmpAdpRegistryIdentitiesRetained boundary ≡ true
_ = refl

_ : Chemical.ap5aStructuralContextRetained boundary ≡ true
_ = refl

_ : Chemical.magnesiumRegistryIdentityRetained boundary ≡ true
_ = refl

_ : Chemical.registryIdentitySelectsSimulationProtonation boundary ≡ false
_ = refl

_ : Chemical.registryIdentitySelectsMgCoordination boundary ≡ false
_ = refl

_ : Chemical.bindingConformationEqualsCatalyticChemistry boundary ≡ false
_ = refl

_ : Chemical.identifierPresenceCreatesChemicalPayment boundary ≡ false
_ = refl
