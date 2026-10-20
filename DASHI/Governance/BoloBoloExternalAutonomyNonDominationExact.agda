module DASHI.Governance.BoloBoloExternalAutonomyNonDominationExact where

open import DASHI.Core.Prelude

import DASHI.Governance.BoloBoloFederationCostComparisonExact as Comparison
import DASHI.Governance.BoloBoloLongitudinalNonDominationExact as Internal
import DASHI.Governance.BoloBoloExternalPrivateControlCrossPollinationExact as External
import DASHI.Governance.BoloBoloExternalChannelDominationNonDescentExact as Channel

------------------------------------------------------------------------
-- INTERNAL NON-DOMINATION + EXTERNAL AUTONOMY
--
-- DASHI synthesis.  The existing longitudinal non-domination certificate is
-- primarily about realised authority inside the target institution.  This
-- owner adds a separate outward-facing audit: an internally democratic /
-- non-dominating federation may still depend on private information systems,
-- capital/ownership channels, or opaque brokerage/relationship structures.
--
-- The inverse is blocked too: observing such dependencies or relations does
-- not establish domination without same-object authority and contestability
-- evidence.
------------------------------------------------------------------------

record ExternalAutonomyAudit : Set₁ where
  constructor external-autonomy-audit
  field
    Target : Set
    target : Target

    InformationInfrastructureDependencyAudited : Set
    informationInfrastructureDependencyWitness :
      InformationInfrastructureDependencyAudited

    CapitalAllocationDependencyAudited : Set
    capitalAllocationDependencyWitness : CapitalAllocationDependencyAudited

    OwnershipStewardshipExposureAudited : Set
    ownershipStewardshipExposureWitness : OwnershipStewardshipExposureAudited

    RelationshipBrokerageExposureAudited : Set
    relationshipBrokerageExposureWitness : RelationshipBrokerageExposureAudited

    SameObjectExternalDecisionAuthorityAudited : Set
    sameObjectExternalDecisionAuthorityWitness :
      SameObjectExternalDecisionAuthorityAudited

    ExternalVetoConstraintAudited : Set
    externalVetoConstraintWitness : ExternalVetoConstraintAudited

    ExternalContestabilityAudited : Set
    externalContestabilityWitness : ExternalContestabilityAudited

    AffectedPartyCoverageAudited : Set
    affectedPartyCoverageWitness : AffectedPartyCoverageAudited

    SourceRoleProvenanceAudited : Set
    sourceRoleProvenanceWitness : SourceRoleProvenanceAudited

open ExternalAutonomyAudit public

record LongitudinalNonDominationWithExternalAutonomy
    (threshold : Nat)
    (model : Comparison.CounterfactualCoordinationCostModel) : Set₂ where
  constructor longitudinal-nondomination-with-external-autonomy
  field
    internalCertificate :
      Internal.JointLongitudinalNonDominationCertificate threshold model

    externalAudit : ExternalAutonomyAudit

    SameTargetExternalAudit : Set
    sameTargetExternalAuditWitness : SameTargetExternalAudit

    ExternalDependencySensitivityPassed : Set
    externalDependencySensitivityWitness : ExternalDependencySensitivityPassed

    ExternalControlCorrectionReopeningPassed : Set
    externalControlCorrectionReopeningWitness :
      ExternalControlCorrectionReopeningPassed

open LongitudinalNonDominationWithExternalAutonomy public

externalPrivateControlBoundaryAnchor : External.ExternalPrivateControlBoundary
externalPrivateControlBoundaryAnchor = External.canonicalExternalPrivateControlBoundary

externalChannelBoundaryAnchor : Channel.ExternalChannelDominationBoundary
externalChannelBoundaryAnchor = Channel.canonicalExternalChannelDominationBoundary

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record ExternalAutonomyNonDominationBoundary : Set where
  constructor external-autonomy-nondomination-boundary
  field
    sameTargetExternalAuditRequired : Bool
    targetExternalAutonomyReceiptStillRequired : Bool
    externalDependencySensitivityRequired : Bool
    affectedPartyCoverageRequired : Bool
    sameObjectExternalAuthorityAuditRequired : Bool
    externalContestabilityAuditRequired : Bool

    internalNonDominationPaysExternalAutonomy : Bool
    externalAutonomyPaysInternalNonDomination : Bool
    informationDependencyPresencePaysExternalControl : Bool
    capitalDependencyPresencePaysExternalControl : Bool
    ownershipExposurePaysExternalControl : Bool
    relationshipExposurePaysExternalControl : Bool
    corporateRolePaysTargetControl : Bool
    commonOwnershipPaysCommonController : Bool
    releasedNetworkArtifactPaysInfluence : Bool
    jointInternalExternalResultPaysPoliticalLegitimacy : Bool
    jointInternalExternalResultPaysEconomicSelfSufficiency : Bool

open ExternalAutonomyNonDominationBoundary public

canonicalExternalAutonomyNonDominationBoundary :
  ExternalAutonomyNonDominationBoundary
canonicalExternalAutonomyNonDominationBoundary =
  external-autonomy-nondomination-boundary
    true true true true true true
    false false false false false false false false false false false
