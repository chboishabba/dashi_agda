module DASHI.Governance.BoloBoloTargetPilotAdmissibilityExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Core.ConsentTemporalExternalityExact as Consent
import DASHI.Core.BenefitBurdenExternalityDistributionExact as Dist
import DASHI.Core.GovernedAdmissibleCostedExperimentChoiceExact as Governed
import DASHI.Governance.BoloBoloPairedGovernanceExperimentExact as Experiment
import DASHI.Governance.BoloBoloCausalJointPromotionExact as CausalJoint
import DASHI.Governance.BoloBoloFederationCostComparisonExact as Comparison

------------------------------------------------------------------------
-- TARGET PILOT ADMISSIBILITY GATE
--
-- Source-neutral DASHI composition.  A good causal design and a favourable
-- result do not authorize changing participants' governance process.
--
-- The existing generic governed-choice owner intentionally has canonical
-- receipts only for initial research and downstream reuse.  There is no
-- generic constructor for interveneDeploy consent.  A bolo paired pilot that
-- actually assigns people to a governance arm must therefore supply a
-- target-specific intervention-scoped governed admission rather than inherit a
-- generic research fixture.
------------------------------------------------------------------------

record TargetPilotAdmissibilityReceipt : Set₁ where
  constructor target-pilot-admissibility-receipt
  field
    trialDesign : Experiment.PairedGovernanceTrialDesign

    governedInterventionAdmission :
      Governed.GovernedAdmissibleAt
        Consent.interveneDeploy
        (Dist.strategyMove Dist.distributionAwareStrategy)

    ParticipantWithdrawalProtocol : Set
    participantWithdrawalProtocolWitness : ParticipantWithdrawalProtocol

    CommunityOrInstitutionalAuthority : Set
    communityOrInstitutionalAuthorityWitness :
      CommunityOrInstitutionalAuthority

    EthicsOrProtocolPermission : Set
    ethicsOrProtocolPermissionWitness : EthicsOrProtocolPermission

    BurdenDistributionAudit : Set
    burdenDistributionAuditWitness : BurdenDistributionAudit

    TemporalExternalityAudit : Set
    temporalExternalityAuditWitness : TemporalExternalityAudit

    ArmAssignmentConsentCoversGovernanceIntervention : Set
    armAssignmentConsentCoversGovernanceInterventionWitness :
      ArmAssignmentConsentCoversGovernanceIntervention

    ExitAndPostTrialRestorationProtocol : Set
    exitAndPostTrialRestorationProtocolWitness :
      ExitAndPostTrialRestorationProtocol

open TargetPilotAdmissibilityReceipt public

------------------------------------------------------------------------
-- Existing exact non-collapse theorem: initial-study consent cannot populate
-- intervention consent merely because the intervention occurs in a study.
------------------------------------------------------------------------

initialResearchConsentCannotAuthoriseIntervention :
  Consent.ConsentFor
    (Consent.scopedConsentState Consent.initialResearch Consent.consentGranted
      Consent.protocolPermissionPresent Consent.authorityPresent
      Consent.benefitSharingAbsent)
    Consent.interveneDeploy → ⊥
initialResearchConsentCannotAuthoriseIntervention =
  Consent.initialConsentDoesNotAuthorizeIntervention

------------------------------------------------------------------------
-- Strongest current target result requiring both evidentiary and execution
-- payments on the same target.  No canonical inhabitant is supplied.
------------------------------------------------------------------------

record AdmissibleCausallyIdentifiedJointGovernanceAdvantage
    (threshold : Nat)
    (model : Comparison.CounterfactualCoordinationCostModel) : Set₂ where
  constructor admissible-causally-identified-joint-governance-advantage
  field
    causalResult :
      CausalJoint.CausallyIdentifiedCoordinationAndNonDominationAdvantage
        threshold model
    pilotAdmissibility : TargetPilotAdmissibilityReceipt

    SameTargetBinding : Set
    sameTargetBindingWitness : SameTargetBinding

    StudyExecutionMatchesPredeclaredDesign : Set
    studyExecutionMatchesPredeclaredDesignWitness :
      StudyExecutionMatchesPredeclaredDesign

open AdmissibleCausallyIdentifiedJointGovernanceAdvantage public

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record TargetPilotAdmissibilityBoundary : Set where
  constructor target-pilot-admissibility-boundary
  field
    interventionScopedGovernedAdmissionRequired : Bool
    initialResearchConsentAutomaticallyAuthorisesPilotIntervention : Bool
    downstreamReuseConsentAutomaticallyAuthorisesPilotIntervention : Bool
    causalResultAutomaticallyAuthorisesPilot : Bool
    cheapOrEfficientExperimentAutomaticallyAdmissible : Bool
    communityAuthorityEqualsParticipantConsent : Bool
    protocolPermissionEqualsParticipantConsent : Bool
    withdrawalProtocolRequired : Bool
    burdenDistributionAuditRequired : Bool
    temporalExternalityAuditRequired : Bool
    exitAndRestorationProtocolRequired : Bool
    sameTargetBindingRequired : Bool
    admissibilityCoverageSettlesSubstantiveJustice : Bool

open TargetPilotAdmissibilityBoundary public

canonicalTargetPilotAdmissibilityBoundary : TargetPilotAdmissibilityBoundary
canonicalTargetPilotAdmissibilityBoundary =
  target-pilot-admissibility-boundary
    true
    false
    false
    false
    false
    false
    false
    true
    true
    true
    true
    true
    false

canonicalBoloTargetPilotAdmissibilityReceipt : GenericReceipt.GenericReceipt
canonicalBoloTargetPilotAdmissibilityReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo target paired-pilot admissibility gate"
    "DASHI.Governance.BoloBoloTargetPilotAdmissibilityExact"
    "TargetPilotAdmissibilityReceipt / AdmissibleCausallyIdentifiedJointGovernanceAdvantage"
    "binds any actual flat-vs-nested governance intervention to the repository's governed-admissibility machinery at interveneDeploy scope and additionally requires withdrawal, community/institutional authority, ethics/protocol permission, burden-distribution, temporal-externality, arm-assignment-consent and exit/restoration receipts on the same target"
    "initial-study or reuse consent cannot authorize the governance intervention; a causal certificate, efficient design, protocol permission or institutional authority does not substitute for participant consent; admissibility coverage still does not settle substantive justice"
    "agda -i . DASHI/Governance/BoloBoloTargetPilotAdmissibilityRegression.agda"
