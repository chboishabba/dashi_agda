module DASHI.PlanningArchitectureSituatedCrossPollinationValidation where

open import DASHI.Core.Prelude

import DASHI.Planning.SituatedBuiltEnvironmentCrossPollinationExact as Situated
import DASHI.Planning.ParticipatoryPlanningGovernanceExact as Participation
import DASHI.Planning.PlanningPolicyBundleAffordanceExact as Policy
import DASHI.Planning.PlanningConflictResidualExact as Conflict

------------------------------------------------------------------------
-- FOCUSED VALIDATION SURFACE
------------------------------------------------------------------------

coarsePlanningStillCannotRecoverSituatedConsumer :
  Situated.INF.FactorsThrough
    Situated.planningSurface
    Situated.situatedConsumerSignature → ⊥
coarsePlanningStillCannotRecoverSituatedConsumer =
  Situated.coarseSituatedPlanningSurfaceCannotRecoverConsumerSignature

sameGeometryStillDoesNotDeterminePublicSpaceInstitution :
  Situated.Ecology.built
      (Policy.publicSpaceEcology Situated.BC.initialPilot) ≡
    Situated.Ecology.built
      (Policy.publicSpaceEcology Situated.BC.postPublicSpaceAmendment)
  ×
  (Situated.Ecology.institution
      (Policy.publicSpaceEcology Situated.BC.initialPilot) ≡
    Situated.Ecology.institution
      (Policy.publicSpaceEcology Situated.BC.postPublicSpaceAmendment) → ⊥)
sameGeometryStillDoesNotDeterminePublicSpaceInstitution =
  Policy.sameGeometryDoesNotDeterminePublicSpaceInstitution

consultationStillDoesNotCreateMetaRuleAuthority :
  Situated.Opposition.CanAlterAdmissionRule
    Situated.Opposition.recognisedOpposition → ⊥
consultationStillDoesNotCreateMetaRuleAuthority =
  Participation.admittedObjectionDoesNotAutomaticallyAlterAdmissionRule

quietOrderStillDoesNotCloseJusticeResidual :
  Conflict.Justice.JusticeClosureCertificate
    Conflict.Rechart.suppressedQuietState → ⊥
quietOrderStillDoesNotCloseJusticeResidual =
  Conflict.quietOrderDoesNotEstablishJusticeClosure

policyLabelStillDoesNotDetermineFullBundle :
  Situated.BC.DecriminalizationLabelPromotesFullBundle → ⊥
policyLabelStillDoesNotDetermineFullBundle =
  Policy.policyLabelDoesNotDetermineFullPlanningBundle

hostileBuiltEffectStillDoesNotProveIntent :
  Situated.Ecology.RestrictiveEffectImpliesIntentPermission → ⊥
hostileBuiltEffectStillDoesNotProveIntent =
  Situated.restrictiveEffectDoesNotManufactureDesignIntent
