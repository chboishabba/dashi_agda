module DASHI.Culture.RastafariItalLoopControlGovernanceExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Core.SharedStateCoalitionReachableEffectExact as Coalition
import DASHI.Culture.RastafariItalBenefitReturnGovernanceExact as Benefit
import DASHI.Culture.RastafariItalReturnFlowCircularityExact as Return
import DASHI.Governance.ConstitutionalAxisResidualCapabilityExact as Constitutional
import DASHI.Planning.AuthoritySovereigntyNonDescentExact as Authority
import DASHI.Planning.CollectiveTerritorialConsentExact as Consent
import DASHI.Planning.NonSubstitutionalReparationExact as Repair
import DASHI.Planning.ParticipatoryPlanningGovernanceExact as Participation

------------------------------------------------------------------------
-- ITAL RETURN-LOOP CONTROL / GOVERNANCE TOPOLOGY
--
-- Cross-pollination owner.  Physical participation in a return/circularity
-- system is kept separate from control of that system.  The generic structure
-- is:
--
--   contribution / labour
--   != title / ownership
--   != destination control
--   != decision rights
--   != benefit receipt
--   != provenance custody
--   != governing authority / institutional power.
--
-- The finite states below are DASHI comparison fixtures.  They do not describe
-- a particular Rastafari or Indigenous community and do not make property law,
-- labour law or sovereignty claims beyond the source owners directly reused.
------------------------------------------------------------------------

data ContributionStatus : Set where
  noContribution labourContribution materialContribution mixedContribution
  : ContributionStatus

data TitleStatus : Set where
  noTitle individualTitle collectiveTitle institutionalTitle : TitleStatus

data DestinationControl : Set where
  noDestinationControl advisoryDestinationInput sharedDestinationControl
  unilateralDestinationControl : DestinationControl

data DecisionRightStatus : Set where
  noDecisionRight consultativeVoice coDecisionRight governingDecisionRight
  : DecisionRightStatus

data BenefitPosition : Set where
  noBenefitPosition incidentalBenefit sharedBenefit controllingBenefit
  : BenefitPosition

data ProvenanceCustody : Set where
  noCustody recordedCustody communityCustody institutionalCustody
  : ProvenanceCustody

data InstitutionalPower : Set where
  lowInstitutionalPower sharedInstitutionalPower dominantInstitutionalPower
  : InstitutionalPower

record LoopControlState : Set where
  constructor loopControlState
  field
    contribution : ContributionStatus
    title : TitleStatus
    destination : DestinationControl
    decision : DecisionRightStatus
    benefitPosition : BenefitPosition
    provenanceCustody : ProvenanceCustody
    institutionalPower : InstitutionalPower

open LoopControlState public

------------------------------------------------------------------------
-- Finite same-participation fixtures.
------------------------------------------------------------------------

labourParticipantOnly : LoopControlState
labourParticipantOnly =
  loopControlState
    labourContribution
    noTitle
    noDestinationControl
    noDecisionRight
    incidentalBenefit
    noCustody
    lowInstitutionalPower

labourParticipantWithVoice : LoopControlState
labourParticipantWithVoice =
  loopControlState
    labourContribution
    noTitle
    advisoryDestinationInput
    consultativeVoice
    sharedBenefit
    recordedCustody
    lowInstitutionalPower

labourParticipantCoDecider : LoopControlState
labourParticipantCoDecider =
  loopControlState
    labourContribution
    collectiveTitle
    sharedDestinationControl
    coDecisionRight
    sharedBenefit
    communityCustody
    sharedInstitutionalPower

labourParticipantInstitutionalGovernor : LoopControlState
labourParticipantInstitutionalGovernor =
  loopControlState
    labourContribution
    institutionalTitle
    unilateralDestinationControl
    governingDecisionRight
    controllingBenefit
    institutionalCustody
    dominantInstitutionalPower

------------------------------------------------------------------------
-- Participation surface cannot recover governance fibres.
------------------------------------------------------------------------

participationCannotRecoverTitle :
  NonFactor.FactorsThrough contribution title → ⊥
participationCannotRecoverTitle =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      labourParticipantOnly labourParticipantCoDecider refl (λ ()))

participationCannotRecoverDestinationControl :
  NonFactor.FactorsThrough contribution destination → ⊥
participationCannotRecoverDestinationControl =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      labourParticipantOnly labourParticipantCoDecider refl (λ ()))

participationCannotRecoverDecisionRights :
  NonFactor.FactorsThrough contribution decision → ⊥
participationCannotRecoverDecisionRights =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      labourParticipantOnly labourParticipantCoDecider refl (λ ()))

participationCannotRecoverBenefitPosition :
  NonFactor.FactorsThrough contribution benefitPosition → ⊥
participationCannotRecoverBenefitPosition =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      labourParticipantOnly labourParticipantWithVoice refl (λ ()))

participationCannotRecoverProvenanceCustody :
  NonFactor.FactorsThrough contribution provenanceCustody → ⊥
participationCannotRecoverProvenanceCustody =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      labourParticipantOnly labourParticipantWithVoice refl (λ ()))

participationCannotRecoverInstitutionalPower :
  NonFactor.FactorsThrough contribution institutionalPower → ⊥
participationCannotRecoverInstitutionalPower =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      labourParticipantOnly labourParticipantInstitutionalGovernor refl (λ ()))

------------------------------------------------------------------------
-- Even co-decision is not definitionally governing authority.
------------------------------------------------------------------------

coDecisionStillNotGoverningAuthority :
  Participation.stageLevel Participation.coDecidingStage ≡
  Participation.stageLevel Participation.governingStage → ⊥
coDecisionStillNotGoverningAuthority =
  Participation.coDecidingIsNotDefinitionallyGoverning

consultationStillNotConsent :
  Consent.CollectiveConsentEnvelope.stage Consent.consultationOnly ≡
  Consent.consentGiven → ⊥
consultationStillNotConsent = Consent.consultedIsNotConsentGiven

------------------------------------------------------------------------
-- Title and administrative control do not exhaust authority/custody.
------------------------------------------------------------------------

propertyTitleStillDoesNotExhaustCustodialRelation :
  Authority.SovereigntyAuthorityBoundary.propertyTitleExhaustsCustodialRelation
    Authority.canonicalSovereigntyAuthorityBoundary
  ≡ false
propertyTitleStillDoesNotExhaustCustodialRelation = refl

effectiveControlStillDoesNotImplyVoluntaryCession :
  Authority.SovereigntyAuthorityBoundary.effectiveControlImpliesVoluntaryCession
    Authority.canonicalSovereigntyAuthorityBoundary
  ≡ false
effectiveControlStillDoesNotImplyVoluntaryCession = refl

------------------------------------------------------------------------
-- Benefit/compensation does not manufacture control rights.
------------------------------------------------------------------------

benefitReturnStillCannotRecoverAuthority :
  NonFactor.FactorsThrough Benefit.benefit Benefit.authority → ⊥
benefitReturnStillCannotRecoverAuthority =
  Benefit.benefitReturnCannotRecoverAuthority

compensationStillDoesNotCreateDecisionRights :
  Repair.ReparativeBundle.status Repair.compensationOnly Repair.decisionRightsAxis
  ≡ Repair.repaired → ⊥
compensationStillDoesNotCreateDecisionRights =
  Repair.compensationDoesNotCreateDecisionRights

------------------------------------------------------------------------
-- Coalition / system-level cross-pollination.
--
-- The security source owner is not a cultural theorem.  We reuse only its
-- generic closure lesson: individually bounded actors need not bound a
-- coalition.  In a circular system, therefore, per-actor role labels are not a
-- proof that the combined reachable control topology has been audited.
------------------------------------------------------------------------

individualBoundsStillDoNotImplyCollectiveBounds :
  Coalition.SharedStateCoalitionBoundary.individualBoundsImplyCollectiveBounds
    Coalition.canonicalSharedStateCoalitionBoundary
  ≡ false
individualBoundsStillDoNotImplyCollectiveBounds = refl

------------------------------------------------------------------------
-- Unresolved affected-party/governance residuals contract irreversible power.
------------------------------------------------------------------------

unresolvedGovernanceResidualStillBlocksIrreversibleCapability :
  Constitutional.CapabilityAvailable
    Constitutional.criticalUnresolved
    Constitutional.irreversibleHighImpact → ⊥
unresolvedGovernanceResidualStillBlocksIrreversibleCapability =
  Constitutional.unresolvedCriticalResidualBlocksIrreversibleCapability

------------------------------------------------------------------------
-- Link back to Ital return-flow vocabulary without promoting return kind into
-- a control allocation.
------------------------------------------------------------------------

communityRedistributionKind : Return.ReturnKind
communityRedistributionKind = Return.communityRedistribution

data ParticipatesInCircularSystemImpliesGovernsSystem : Set where

data MaterialOwnershipImpliesDestinationAuthority : Set where

data LabourContributionImpliesBenefitControl : Set where

data BenefitReceiptImpliesDecisionRight : Set where

data ProvenanceRecordImpliesCustodialAuthority : Set where

data CommunityRedistributionImpliesCommunityGovernance : Set where

participationDoesNotAutoPromoteToGovernance :
  ParticipatesInCircularSystemImpliesGovernsSystem → ⊥
participationDoesNotAutoPromoteToGovernance ()

materialOwnershipDoesNotAutoPromoteToDestinationAuthority :
  MaterialOwnershipImpliesDestinationAuthority → ⊥
materialOwnershipDoesNotAutoPromoteToDestinationAuthority ()

labourContributionDoesNotAutoPromoteToBenefitControl :
  LabourContributionImpliesBenefitControl → ⊥
labourContributionDoesNotAutoPromoteToBenefitControl ()

benefitReceiptDoesNotAutoPromoteToDecisionRight :
  BenefitReceiptImpliesDecisionRight → ⊥
benefitReceiptDoesNotAutoPromoteToDecisionRight ()

provenanceRecordDoesNotAutoPromoteToCustodialAuthority :
  ProvenanceRecordImpliesCustodialAuthority → ⊥
provenanceRecordDoesNotAutoPromoteToCustodialAuthority ()

communityRedistributionDoesNotAutoPromoteToCommunityGovernance :
  CommunityRedistributionImpliesCommunityGovernance → ⊥
communityRedistributionDoesNotAutoPromoteToCommunityGovernance ()

record ItalLoopControlGovernanceBoundary : Set where
  constructor italLoopControlGovernanceBoundary
  field
    participationEqualsGovernance : Bool
    participationEqualsGovernanceIsFalse : participationEqualsGovernance ≡ false

    ownershipEqualsDestinationControl : Bool
    ownershipEqualsDestinationControlIsFalse : ownershipEqualsDestinationControl ≡ false

    benefitReceiptEqualsDecisionRight : Bool
    benefitReceiptEqualsDecisionRightIsFalse : benefitReceiptEqualsDecisionRight ≡ false

    provenanceRecordEqualsCustodialAuthority : Bool
    provenanceRecordEqualsCustodialAuthorityIsFalse :
      provenanceRecordEqualsCustodialAuthority ≡ false

    circularityAuditIncludesControlTopology : Bool
    circularityAuditIncludesControlTopologyIsTrue :
      circularityAuditIncludesControlTopology ≡ true

canonicalItalLoopControlGovernanceBoundary :
  ItalLoopControlGovernanceBoundary
canonicalItalLoopControlGovernanceBoundary =
  italLoopControlGovernanceBoundary
    false refl
    false refl
    false refl
    false refl
    true refl
