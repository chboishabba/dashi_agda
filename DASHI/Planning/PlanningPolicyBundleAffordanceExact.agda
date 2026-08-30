module DASHI.Planning.PlanningPolicyBundleAffordanceExact where

open import DASHI.Core.Prelude

import DASHI.Biology.SocialEcologicalAffordanceConeExact as Ecology
import DASHI.Governance.BritishColumbiaDecriminalizationBundleExact as BC

------------------------------------------------------------------------
-- PLANNING POLICY BUNDLE -> PUBLIC-SPACE AFFORDANCE SEAM
--
-- A policy label is not a complete intervention description.  The existing BC
-- owner already separates legal protection, public-space rules, policing,
-- service capacity, funding, training, housing and poverty infrastructure.
-- This module exposes that bundle discipline as a reusable planning seam while
-- preserving the source-specific BC object unchanged.
------------------------------------------------------------------------

record GenericPlanningPolicyBundle : Set₁ where
  constructor genericPlanningPolicyBundle
  field
    LegalRule : Set
    PublicSpaceRule : Set
    EnforcementState : Set
    ServiceCapacity : Set
    FundingState : Set
    InfrastructureState : Set
    Observation : Set

open GenericPlanningPolicyBundle public

bcPlanningBundleShape : GenericPlanningPolicyBundle
bcPlanningBundleShape =
  genericPlanningPolicyBundle
    BC.AxisState
    BC.AxisState
    BC.AxisState
    (BC.AxisState × BC.AxisState)
    BC.AxisState
    (BC.AxisState × BC.AxisState)
    BC.OutcomeObservation

------------------------------------------------------------------------
-- The policy phase can alter the institutional public-space regime while the
-- physical built-space category remains fixed.
------------------------------------------------------------------------

publicSpaceEcology : BC.PolicyPhase → Ecology.Ecology
publicSpaceEcology phase =
  Ecology.ecology
    Ecology.neutralPublicSpace
    Ecology.lowDemandNorms
    (Ecology.bcPublicSpaceRegime phase)
    Ecology.unknownRelation

sameBuiltGeometryAcrossBCPolicyPhases :
  Ecology.built (publicSpaceEcology BC.initialPilot) ≡
  Ecology.built (publicSpaceEcology BC.postPublicSpaceAmendment)
sameBuiltGeometryAcrossBCPolicyPhases = refl

publicSpaceInstitutionChangesAcrossBCPolicyPhases :
  Ecology.institution (publicSpaceEcology BC.initialPilot) ≡
  Ecology.institution (publicSpaceEcology BC.postPublicSpaceAmendment) → ⊥
publicSpaceInstitutionChangesAcrossBCPolicyPhases =
  Ecology.bcAmendmentChangesPublicSpaceRegime

sameGeometryDoesNotDeterminePublicSpaceInstitution :
  Ecology.built (publicSpaceEcology BC.initialPilot) ≡
    Ecology.built (publicSpaceEcology BC.postPublicSpaceAmendment)
  ×
  (Ecology.institution (publicSpaceEcology BC.initialPilot) ≡
    Ecology.institution (publicSpaceEcology BC.postPublicSpaceAmendment) → ⊥)
sameGeometryDoesNotDeterminePublicSpaceInstitution =
  refl , publicSpaceInstitutionChangesAcrossBCPolicyPhases

------------------------------------------------------------------------
-- Source-owner non-promotions retained exactly.
------------------------------------------------------------------------

policyLabelDoesNotDetermineFullPlanningBundle :
  BC.DecriminalizationLabelPromotesFullBundle → ⊥
policyLabelDoesNotDetermineFullPlanningBundle = BC.labelDoesNotPromoteFullBundle

observedOutcomeDoesNotSelfIdentifyLegalCause :
  BC.PilotOutcomePromotesLegalReformCausality → ⊥
observedOutcomeDoesNotSelfIdentifyLegalCause =
  BC.outcomeDoesNotPromoteLegalReformCausality

underprovisionDoesNotProvePolicyClassImpossibility :
  BC.UnderprovisionPromotesImpossibilityOfReform → ⊥
underprovisionDoesNotProvePolicyClassImpossibility =
  BC.underprovisionDoesNotPromoteImpossibilityOfReform

visiblePublicUseDoesNotSelfIdentifyPolicyCause :
  BC.VisiblePublicUsePromotesDecriminalizationCause → ⊥
visiblePublicUseDoesNotSelfIdentifyPolicyCause =
  BC.visiblePublicUseDoesNotPromoteDecriminalizationCause

------------------------------------------------------------------------
-- Generic claim boundary for later housing, zoning, climate, transport and
-- large-load/data-centre instantiations.
------------------------------------------------------------------------

data PolicyLabelDeterminesImplementationPermission : Set where
data LegalRuleDeterminesSupportiveEcologyPermission : Set where

data PublicSpaceRuleDeterminesHousingInfrastructurePermission : Set where

policyLabelCannotAutoPromoteToImplementation :
  PolicyLabelDeterminesImplementationPermission → ⊥
policyLabelCannotAutoPromoteToImplementation ()

legalRuleCannotAutoPromoteToSupportiveEcology :
  LegalRuleDeterminesSupportiveEcologyPermission → ⊥
legalRuleCannotAutoPromoteToSupportiveEcology ()

publicSpaceRuleCannotAutoPromoteToHousingInfrastructure :
  PublicSpaceRuleDeterminesHousingInfrastructurePermission → ⊥
publicSpaceRuleCannotAutoPromoteToHousingInfrastructure ()
