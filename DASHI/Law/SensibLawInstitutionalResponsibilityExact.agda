module DASHI.Law.SensibLawInstitutionalResponsibilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

------------------------------------------------------------------------
-- INSTITUTIONAL ACTION / RESPONSIBILITY SEPARATION
--
-- This owner is deliberately non-adjudicative.  It keeps causal contribution,
-- permission, authority, enforcement, justification, knowledge, intent,
-- capacity to refuse, role and responsibility as separate coordinates.  It
-- does not assign culpability to any historical or contemporary actor.
------------------------------------------------------------------------

data CauseState : Set where
  causalContributionPresent causalContributionAbsent : CauseState

data PermissionState : Set where
  permitted prohibited : PermissionState

data AuthorityState : Set where
  authorised unauthorised : AuthorityState

data EnforcementState : Set where
  enforced notEnforced : EnforcementState

data JustificationState : Set where
  justified notJustified : JustificationState

data KnowledgeState : Set where
  knowledgePresent knowledgeAbsent knowledgeUnresolved : KnowledgeState

data IntentState : Set where
  intentPresent intentAbsent intentUnresolved : IntentState

data CapacityToRefuseState : Set where
  refusalCapacityPresent refusalCapacityAbsent refusalCapacityUnresolved : CapacityToRefuseState

data RoleState : Set where
  policyArchitectRole implementationRole supportRole unrelatedRole : RoleState

data ResponsibilityState : Set where
  responsibilityEstablished responsibilityNotEstablished responsibilityUnresolved : ResponsibilityState

record InstitutionalActionStatus : Set where
  constructor institutionalActionStatus
  field
    cause : CauseState
    permission : PermissionState
    authority : AuthorityState
    enforcement : EnforcementState
    justification : JustificationState
    knowledge : KnowledgeState
    intent : IntentState
    capacityToRefuse : CapacityToRefuseState
    role : RoleState
    responsibility : ResponsibilityState

open InstitutionalActionStatus public

record InstitutionalResponsibilityBoundary : Set where
  constructor institutionalResponsibilityBoundary
  field
    causedAutomaticallyAuthorised : Bool
    authorisedAutomaticallyJustified : Bool
    lawfulAutomaticallyMorallyJustified : Bool
    smallContributionAutomaticallyNoContribution : Bool
    distributedCausationAutomaticallyNoCausation : Bool
    roleObligationAutomaticallyCompleteResponsibilityAnswer : Bool
    notPolicyArchitectAutomaticallyNoResponsibility : Bool
    responsibilityRequiresAdditionalCoordinates : Bool

open InstitutionalResponsibilityBoundary public

canonicalInstitutionalResponsibilityBoundary : InstitutionalResponsibilityBoundary
canonicalInstitutionalResponsibilityBoundary =
  institutionalResponsibilityBoundary
    false
    false
    false
    false
    false
    false
    false
    true
