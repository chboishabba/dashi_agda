module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCollectiveVariableDefinitionAcquisitionValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCollectiveVariableDefinitionAcquisitionExact as Owner

boundary : Owner.AdKCollectiveVariableDefinitionAcquisitionBoundary
boundary = Owner.canonicalAdKCollectiveVariableDefinitionAcquisitionBoundary

thetaOneDefinitionPaid : Owner.thetaOneDefinitionPaid boundary ≡ true
thetaOneDefinitionPaid = refl

thetaTwoDefinitionPaid : Owner.thetaTwoDefinitionPaid boundary ≡ true
thetaTwoDefinitionPaid = refl

dLnDefinitionPaid : Owner.dLnDefinitionPaid boundary ≡ true
dLnDefinitionPaid = refl

centerOfMassRolePaid : Owner.centerOfMassRolePaid boundary ≡ true
centerOfMassRolePaid = refl

sameVariableNameImpliesSameObservableDefinition :
  Owner.sameVariableNameImpliesSameObservableDefinition boundary ≡ false
sameVariableNameImpliesSameObservableDefinition = refl

collectiveVariableDefinitionCreatesNamedStateValue :
  Owner.collectiveVariableDefinitionCreatesNamedStateValue boundary ≡ false
collectiveVariableDefinitionCreatesNamedStateValue = refl

identityMetadataCreatesObservableDefinition :
  Owner.identityMetadataCreatesObservableDefinition boundary ≡ false
identityMetadataCreatesObservableDefinition = refl
