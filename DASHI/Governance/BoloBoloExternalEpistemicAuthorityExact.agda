module DASHI.Governance.BoloBoloExternalEpistemicAuthorityExact where

open import DASHI.Core.Prelude

import DASHI.Governance.DecisionPotentialAuthorityOrthogonalityExact as Orthogonality
import DASHI.Governance.BoloBoloExternalPrivateControlCrossPollinationExact as External

------------------------------------------------------------------------
-- EXTERNAL EPISTEMIC / FRAMING POWER != FORMAL AUTHORITY
--
-- DASHI synthesis.  External information systems and investors may alter what
-- becomes legible, salient, comparable, actionable or costly without thereby
-- holding formal decision authority.  Conversely, formal authority does not
-- determine the information/framing landscape presented to decision-makers.
--
-- The generic orthogonality theorem is repo-local DASHI machinery.  The
-- surrounding Palantir / asset-manager sources motivate empirical audit
-- coordinates only; they are not authors of the theorem and do not establish a
-- target-specific framing effect.
------------------------------------------------------------------------

potentialAuthorityBoundaryAnchor : Orthogonality.PotentialAuthorityBoundary
potentialAuthorityBoundaryAnchor = Orthogonality.canonicalPotentialAuthorityBoundary

externalSourceBoundaryAnchor : External.ExternalPrivateControlBoundary
externalSourceBoundaryAnchor = External.canonicalExternalPrivateControlBoundary

record ExternalEpistemicAuthorityAudit : Set₁ where
  constructor external-epistemic-authority-audit
  field
    Target : Set
    target : Target

    DataLegibilityAudited : Set
    dataLegibilityWitness : DataLegibilityAudited

    ClassificationAndOntologyAudited : Set
    classificationAndOntologyWitness : ClassificationAndOntologyAudited

    AgendaSalienceAudited : Set
    agendaSalienceWitness : AgendaSalienceAudited

    OptionSetPresentationAudited : Set
    optionSetPresentationWitness : OptionSetPresentationAudited

    InvestorOrFunderExpectationAudited : Set
    investorOrFunderExpectationWitness : InvestorOrFunderExpectationAudited

    FormalDecisionAuthorityAudited : Set
    formalDecisionAuthorityWitness : FormalDecisionAuthorityAudited

    SubjectOrAffectedPartyContestabilityAudited : Set
    subjectOrAffectedPartyContestabilityWitness :
      SubjectOrAffectedPartyContestabilityAudited

open ExternalEpistemicAuthorityAudit public

record ExternalEpistemicAuthorityBoundary : Set where
  constructor external-epistemic-authority-boundary
  field
    epistemicAndFormalAuthorityAuditedSeparately : Bool
    genericPotentialAuthorityOrthogonalityReused : Bool
    targetFramingMeasurementStillRequired : Bool

    epistemicFramingPaysFormalAuthority : Bool
    formalAuthorityPaysEpistemicFraming : Bool
    platformLegibilityCapabilityPaysObservedFramingEffect : Bool
    investorExpectationDocumentPaysTargetControl : Bool
    capitalProviderPresencePaysAgendaControl : Bool
    classificationCapabilityPaysCorrectClassification : Bool
    auditLoggingPaysAffectedPartyContestability : Bool
    epistemicInfluenceAutomaticallyPaysDomination : Bool

open ExternalEpistemicAuthorityBoundary public

canonicalExternalEpistemicAuthorityBoundary : ExternalEpistemicAuthorityBoundary
canonicalExternalEpistemicAuthorityBoundary =
  external-epistemic-authority-boundary
    true true true
    false false false false false false false false
