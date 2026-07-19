module DASHI.Biology.Levin.ComponentCausalRoleBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.ProblemSpaceAgency as Problem
import DASHI.Biology.Levin.ConstitutiveInteractiveAutonomy as Autonomy
import DASHI.Biology.Levin.ElectrochemicalBodyConsortium as Consortium

------------------------------------------------------------------------
-- Distinguish causal participation from necessity, sufficiency, control,
-- authorship, and organism-level policy ownership.

record ComponentCausalRole : Set where
  field
    componentSpecified : Bool
    organismLevelOutcomeSpecified : Bool
    interventionSpecified : Bool
    influenceObserved : Bool
    necessityTested : Bool
    sufficiencyTested : Bool
    controlTested : Bool
    authorshipClaimTested : Bool
    scaleSpecified : Bool
    problemSpaceSpecified : Bool

record ComponentCausalRoleBoundary : Set where
  field
    problemSpaceBoundary : Problem.ProblemSpaceAgencyBoundary
    autonomyBoundary : Autonomy.ConstitutiveInteractiveAutonomyBoundary
    consortiumBoundary : Consortium.ElectrochemicalBodyConsortiumBoundary
    influenceDoesNotImplyControl : Bool
    necessityDoesNotImplySufficiency : Bool
    biasDoesNotImplyAuthorship : Bool
    localGoalDoesNotImplyOrganismLevelPolicyOwnership : Bool
    componentCountDoesNotDetermineCausalWeight : Bool
    organismLevelPolicyMayResolveMultipleSubsystemTendencies : Bool
    interpretation : String

canonicalComponentCausalRoleBoundary : ComponentCausalRoleBoundary
canonicalComponentCausalRoleBoundary = record
  { problemSpaceBoundary = Problem.canonicalProblemSpaceAgencyBoundary
  ; autonomyBoundary = Autonomy.canonicalConstitutiveInteractiveAutonomyBoundary
  ; consortiumBoundary = Consortium.canonicalElectrochemicalBodyConsortiumBoundary
  ; influenceDoesNotImplyControl = true
  ; necessityDoesNotImplySufficiency = true
  ; biasDoesNotImplyAuthorship = true
  ; localGoalDoesNotImplyOrganismLevelPolicyOwnership = true
  ; componentCountDoesNotDetermineCausalWeight = true
  ; organismLevelPolicyMayResolveMultipleSubsystemTendencies = true
  ; interpretation = "Subsystems may influence, constrain, enable, or bias organism-level behaviour, but influence, necessity, sufficiency, control, authorship, and policy ownership remain distinct intervention-indexed causal roles"
  }

MicrobialInfluenceImpliesMicrobialControl : Bool
MicrobialInfluenceImpliesMicrobialControl = false

OrganelleHomeostasisImpliesHostAuthorship : Bool
OrganelleHomeostasisImpliesHostAuthorship = false
