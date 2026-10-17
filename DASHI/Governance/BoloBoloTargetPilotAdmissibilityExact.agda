module DASHI.Governance.BoloBoloTargetPilotAdmissibilityExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Core.ConsentTemporalExternalityExact as Consent
import DASHI.Core.GovernedAdmissibleCostedExperimentChoiceExact as Governed
import DASHI.Governance.BoloBoloPairedGovernanceExperimentExact as Experiment
import DASHI.Governance.BoloBoloCausalJointPromotionExact as CausalJoint
import DASHI.Governance.BoloBoloFederationCostComparisonExact as Comparison

------------------------------------------------------------------------
-- TARGET PILOT ADMISSIBILITY GATE
--
-- Source-neutral DASHI composition. A good causal design and a favourable
-- result do not authorize changing participants' governance process.
--
-- The existing generic governed-choice owner has canonical receipts only for
-- initial research and downstream reuse. Its consent datatype deliberately has
-- no generic interveneDeploy constructor. We therefore reuse its non-collapse
-- laws while requiring a target-specific proof-relevant intervention admission
-- here. This avoids both bad outcomes:
--   * initial-study consent silently becoming intervention consent; and
--   * making every future pilot uninhabitable by demanding a closed generic
--     constructor which cannot exist without changing the Core API.
------------------------------------------------------------------------

record PilotInterventionGovernedAdmission : Set₁ where
  constructor pilot-intervention-governed-admission
  field
    EpistemicAdequacy : Set
    epistemicAdequacyWitness : EpistemicAdequacy

    InstitutionalOrCommunityAuthority : Set
    institutionalOrCommunityAuthorityWitness :
      InstitutionalOrCommunityAuthority

    ProtocolPermission : Set
    protocolPermissionWitness : ProtocolPermission

    InterventionScopedParticipantConsent : Set
    interventionScopedParticipantConsentWitness :
      InterventionScopedParticipantConsent

    ContinuingWithdrawalRight : Set
    continuingWithdrawalRightWitness : ContinuingWithdrawalRight

    ObligationsCoverage : Set
    obligationsCoverageWitness : ObligationsCoverage

    ExternalityCoverage : Set
    externalityCoverageWitness : ExternalityCoverage

    DistributionCoverage : Set
    distributionCoverageWitness : DistributionCoverage

    TemporalAndIntergenerationalCoverage : Set
    temporalAndIntergenerationalCoverageWitness :
      TemporalAndIntergenerationalCoverage

    ExitAndPostTrialRestoration : Set
    exitAndPostTrialRestorationWitness : ExitAndPostTrialRestoration

open PilotInterventionGovernedAdmission public

record TargetPilotAdmissibilityReceipt : Set₁ where
  constructor target-pilot-admissibility-receipt
  field
    trialDesign : Experiment.PairedGovernanceTrialDesign
    interventionAdmission : PilotInterventionGovernedAdmission

    SameTargetAdmission : Set
    sameTargetAdmissionWitness : SameTargetAdmission

    ArmAssignmentConsentCoversGovernanceIntervention : Set
    armAssignmentConsentCoversGovernanceInterventionWitness :
      ArmAssignmentConsentCoversGovernanceIntervention

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

genericGovernedBoundaryAnchor : Governed.GovernedAdmissibleCostedChoiceBoundary
genericGovernedBoundaryAnchor =
  Governed.canonicalGovernedAdmissibleCostedChoiceBoundary

------------------------------------------------------------------------
-- Strongest current target result requiring both evidentiary and execution
-- payments on the same target. No canonical inhabitant is supplied.
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
    genericCoreProvidesCanonicalInterventionConsent : Bool
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
    "PilotInterventionGovernedAdmission / TargetPilotAdmissibilityReceipt / AdmissibleCausallyIdentifiedJointGovernanceAdvantage"
    "reuses the generic consent/authority/admissibility non-collapse laws but requires a target-specific proof-relevant intervention admission for an actual flat-vs-nested governance assignment: epistemic adequacy, community/institutional authority, protocol permission, intervention-scoped participant consent, continuing withdrawal, obligations, externalities, distribution, temporal/intergenerational coverage, exit/restoration and same-target binding"
    "the generic Core deliberately supplies no canonical intervention-consent constructor; initial-study or reuse consent cannot authorize the governance intervention; a causal certificate, efficient design, protocol permission or institutional authority does not substitute for participant consent; admissibility coverage still does not settle substantive justice"
    "agda -i . DASHI/Governance/BoloBoloTargetPilotAdmissibilityRegression.agda"
