module DASHI.PlanningArchitectureSituatedCrossPollinationValidation where

open import DASHI.Core.Prelude

import DASHI.Biology.SocialEcologicalAffordanceConeExact as Ecology
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.BritishColumbiaDecriminalizationBundleExact as BC
import DASHI.Governance.InstitutionPreservingRechartAntiSublationExact as Rechart
import DASHI.Governance.OppositionInterfaceAntiDomesticationExact as Opposition
import DASHI.Governance.PeaceJusticeResidualNonFactorabilityExact as Justice
import DASHI.Planning.SituatedBuiltEnvironmentCrossPollinationExact as Situated
import DASHI.Planning.ParticipatoryPlanningGovernanceExact as Participation
import DASHI.Planning.PlanningPolicyBundleAffordanceExact as Policy
import DASHI.Planning.PlanningConflictResidualExact as Conflict

------------------------------------------------------------------------
-- FOCUSED VALIDATION SURFACE
------------------------------------------------------------------------

coarsePlanningStillCannotRecoverSituatedConsumer :
  INF.FactorsThrough
    Situated.planningSurface
    Situated.situatedConsumerSignature → ⊥
coarsePlanningStillCannotRecoverSituatedConsumer =
  Situated.coarseSituatedPlanningSurfaceCannotRecoverConsumerSignature

sameGeometryStillDoesNotDeterminePublicSpaceInstitution :
  Ecology.built (Policy.publicSpaceEcology BC.initialPilot) ≡
    Ecology.built (Policy.publicSpaceEcology BC.postPublicSpaceAmendment)
  ×
  (Ecology.institution (Policy.publicSpaceEcology BC.initialPilot) ≡
    Ecology.institution (Policy.publicSpaceEcology BC.postPublicSpaceAmendment) → ⊥)
sameGeometryStillDoesNotDeterminePublicSpaceInstitution =
  Policy.sameGeometryDoesNotDeterminePublicSpaceInstitution

consultationStillDoesNotCreateMetaRuleAuthority :
  Opposition.CanAlterAdmissionRule Opposition.recognisedOpposition → ⊥
consultationStillDoesNotCreateMetaRuleAuthority =
  Participation.admittedObjectionDoesNotAutomaticallyAlterAdmissionRule

quietOrderStillDoesNotCloseJusticeResidual :
  Justice.JusticeClosureCertificate Rechart.suppressedQuietState → ⊥
quietOrderStillDoesNotCloseJusticeResidual =
  Conflict.quietOrderDoesNotEstablishJusticeClosure

policyLabelStillDoesNotDetermineFullBundle :
  BC.DecriminalizationLabelPromotesFullBundle → ⊥
policyLabelStillDoesNotDetermineFullBundle =
  Policy.policyLabelDoesNotDetermineFullPlanningBundle

hostileBuiltEffectStillDoesNotProveIntent :
  Ecology.RestrictiveEffectImpliesIntentPermission → ⊥
hostileBuiltEffectStillDoesNotProveIntent =
  Situated.restrictiveEffectDoesNotManufactureDesignIntent
