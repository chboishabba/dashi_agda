module DASHI.Cognition.PNF.GrokkingSparseActiveColouringRoutingRegression where

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.GrokkingSparseActiveColouringRoutingExact as Bridge

availableCapacityExceedsActiveSupport :
  Bridge.activeSupport Bridge.structuredSparseWitness <
  Bridge.availableCapacity Bridge.structuredSparseWitness
availableCapacityExceedsActiveSupport =
  Bridge.structuredSparseUsesStrictSubset

inactiveForOneInputDoesNotMeanGloballyRedundant :
  Bridge.inactiveForCurrentInput Bridge.conditionallyUsefulUnit ≡ true ×
  Bridge.usefulOnAnotherInput Bridge.conditionallyUsefulUnit ≡ true
inactiveForOneInputDoesNotMeanGloballyRedundant =
  Bridge.conditionalUseWitness

trainingFitDoesNotDetermineSparseStructuralRoute :
  Bridge.trainingFitSame Bridge.memorizerRoute Bridge.characterRoute ≡ true ×
  Bridge.structuralDefect Bridge.characterRoute <
  Bridge.structuralDefect Bridge.memorizerRoute
trainingFitDoesNotDetermineSparseStructuralRoute =
  Bridge.fitEqualButStructuralRouteImproves

colouringWitnessIsAnalogyNotIdentity :
  Bridge.colouringConflictFreeBatchWitness ≡ true ×
  Bridge.grokkingLiterallyMinimisesChromaticNumber ≡ false
colouringWitnessIsAnalogyNotIdentity =
  Bridge.colouringAnalogyBoundary

largeCandidateFamilyCanCoexistWithSparseAction :
  Bridge.largeCandidateFamily Bridge.colouringRoutingWitness ≡ true ×
  Bridge.sparseCompatibleAction Bridge.colouringRoutingWitness ≡ true
largeCandidateFamilyCanCoexistWithSparseAction =
  Bridge.colouringCandidateActionWitness
