module DASHI.Biology.Levin.ConstitutiveInteractiveAutonomy where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.ProblemSpaceAgency as Problem
import DASHI.Biology.Levin.SeparableBoundaryPersistence as Boundary
import DASHI.Biology.Levin.MultiscaleIdentityDissociation as Identity

record AutonomyObservation : Set where
  field
    recurrentInternalDependence : Bool
    boundaryMaintenanceObserved : Bool
    environmentalDependenceMeasured : Bool
    interventionRecoveryMeasured : Bool
    goalScopeMeasured : Bool
    selfOtherClassificationObserved : Bool
    scaleExplicit : Bool
    problemSpaceExplicit : Bool

record ConstitutiveInteractiveAutonomyBoundary : Set where
  field
    problemSpaceBoundary : Problem.ProblemSpaceAgencyBoundary
    separabilityType     : Set
    identityBoundary     : Identity.MultiscaleIdentityDissociationBoundary
    constitutiveAutonomyNotIsolation : Bool
    interactiveAutonomyNotIndependence : Bool
    observerBoundaryNotNecessarilySystemBoundary : Bool
    systemBoundaryNotSharpByDefinition : Bool
    cognitiveLightConeRequiresGoalWitness : Bool
    contractedGoalScopeNotMoralSelfishness : Bool
    cancerInterpretationNotUniversal : Bool
    interpretation : String

canonicalConstitutiveInteractiveAutonomyBoundary :
  ConstitutiveInteractiveAutonomyBoundary
canonicalConstitutiveInteractiveAutonomyBoundary = record
  { problemSpaceBoundary = Problem.canonicalProblemSpaceAgencyBoundary
  ; separabilityType = Boundary.SeparableBoundaryPersistence
  ; identityBoundary = Identity.canonicalMultiscaleIdentityDissociationBoundary
  ; constitutiveAutonomyNotIsolation = true
  ; interactiveAutonomyNotIndependence = true
  ; observerBoundaryNotNecessarilySystemBoundary = true
  ; systemBoundaryNotSharpByDefinition = true
  ; cognitiveLightConeRequiresGoalWitness = true
  ; contractedGoalScopeNotMoralSelfishness = true
  ; cancerInterpretationNotUniversal = true
  ; interpretation = "A candidate self is indexed by recurrent internal organisation, maintained boundaries, environmental coupling and the scale of states actively regulated; no single external partition is privileged by definition"
  }
