module DASHI.Cognition.PNF.SensibLawCorporateConstraintAndEvidenceProvenanceExact where

------------------------------------------------------------------------
-- CORPORATE CONSTRAINT / ENFORCEMENT / EVIDENCE PROVENANCE
--
-- This module formalises the difference between prohibition-on-the-books and
-- effective constraint, and separates contemporaneous internal evidence from
-- party allegations/denials. It does not assert subjective intent of any named
-- corporation and does not encode a particular Meta allegation as adjudicated
-- fact.
--
-- Sources / motivation:
--   * Stafford Beer, POSIWID heuristic; typed source boundary owned by
--     DASHI.Core.OperationalSystemBehaviourSemanticsExact.
--   * Corporations Act 2001 (Cth), stable Australian legislation identifier
--     C2004A00818, as a calibration example of statutory contravention / civil
--     penalty architecture. No proposition below purports to summarise every
--     Corporations Act enforcement pathway.
--
-- The optimisation and evidence-type structures are DASHI formal machinery.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawTypedLegalAuthorityEdgeExact as Edge
import DASHI.Core.OperationalSystemBehaviourSemanticsExact as Operational

------------------------------------------------------------------------
-- Legal enforcement chain. Economics may annotate this graph only after the
-- legal path is represented.
------------------------------------------------------------------------

data EnforcementStage : Set where
  conduct
  statutoryElement
  contravention
  regulatorJurisdiction
  causeOfActionOrEnforcementPower
  proofRequirement
  defenceOrException
  liability
  availablePenalty
  penaltyDiscretion
  appeal
  collection
  behaviouralOrder
  : EnforcementStage

record EnforcementEdge : Set where
  constructor enforcement-edge
  field
    edgeId : String
    fromStage : EnforcementStage
    toStage : EnforcementStage
    proposition : String
    authority : Edge.SourceIdentity
    sourceSupportsEdge : Bool

open EnforcementEdge public

data ProhibitionAutomaticallyMeansEffectiveConstraint : Set where
data MaximumPenaltyEqualsExpectedPenalty : Set where
data NominalPenaltyEqualsEconomicDeterrence : Set where
data DetectionProbabilityIsLegalRule : Set where

prohibitionDoesNotAutomaticallyConstrain :
  ProhibitionAutomaticallyMeansEffectiveConstraint → ⊥
prohibitionDoesNotAutomaticallyConstrain ()

maximumIsNotExpectedPenaltyByDefinition : MaximumPenaltyEqualsExpectedPenalty → ⊥
maximumIsNotExpectedPenaltyByDefinition ()

nominalAmountDoesNotDetermineDeterrence : NominalPenaltyEqualsEconomicDeterrence → ⊥
nominalAmountDoesNotDetermineDeterrence ()

detectionProbabilityDoesNotBecomeAuthority : DetectionProbabilityIsLegalRule → ⊥
detectionProbabilityDoesNotBecomeAuthority ()

------------------------------------------------------------------------
-- Economic annotations sit over the typed legal graph.
------------------------------------------------------------------------

record EconomicConstraintAnnotation : Set where
  constructor economic-constraint-annotation
  field
    benefitMeasure : String
    detectionEstimate : String
    enforcementConditionalEstimate : String
    sanctionMeasure : String
    litigationOrComplianceCost : String
    reputationalOrBusinessCost : String
    empiricalProvenance : String
    attachedAfterLegalPath : Bool
    attachedAfterLegalPathIsTrue : attachedAfterLegalPath ≡ true

open EconomicConstraintAnnotation public

------------------------------------------------------------------------
-- Transaction-structure search and legislative repair.
------------------------------------------------------------------------

record LegalStructureSearch : Set where
  constructor legal-structure-search
  field
    desiredEconomicEffect : String
    candidateLegalStructure : String
    legalClassificationPath : String
    liabilityOrTaxEffect : String
    authorityPath : String
    lawfulStatusMustBeProved : Bool

open LegalStructureSearch public

record LegislativeRepairCandidate : Set where
  constructor legislative-repair-candidate
  field
    knownEscapeFamily : String
    proposedPredicateChange : String
    intendedCapturedSet : String
    intendedProtectedSet : String
    closesKnownEscapesClaim : Bool
    preservesProtectedSetClaim : Bool
    requiresLegislativeAndConstitutionalValidation : Bool

open LegislativeRepairCandidate public

------------------------------------------------------------------------
-- Evidence provenance: adversarial statements do not erase stronger or weaker
-- sources mechanically. Weighting remains proposition-relative.
------------------------------------------------------------------------

data EvidenceRelation : Set where
  internalContemporaneousRecord
  observedConduct
  expertFinding
  regulatoryFinding
  adjudicatedFact
  partyAllegation
  partyDenial
  postHocPublicStatement
  independentContraryEvidence
  : EvidenceRelation

record EvidenceReceipt : Set where
  constructor evidence-receipt
  field
    proposition : String
    relation : EvidenceRelation
    authorOrInstitution : String
    titleOrArtifact : String
    stableIdentifier : String
    contemporaneous : Bool
    financiallyOrLitigationInterestedSource : Bool
    adjudicated : Bool

open EvidenceReceipt public

data PartyDenialMeansNegation : Set where
data PartyDenialIsIndependentContraryEvidence : Set where
data InternalRecordAutomaticallyProvesWorldTruth : Set where
data RepeatedOperationalEffectAutomaticallyProvesSubjectiveIntent : Set where

partyDenialDoesNotEqualNegation : PartyDenialMeansNegation → ⊥
partyDenialDoesNotEqualNegation ()

partyDenialDoesNotBecomeIndependentEvidence :
  PartyDenialIsIndependentContraryEvidence → ⊥
partyDenialDoesNotBecomeIndependentEvidence ()

internalRecordDoesNotAutomaticallyProveWorldTruth :
  InternalRecordAutomaticallyProvesWorldTruth → ⊥
internalRecordDoesNotAutomaticallyProveWorldTruth ()

systemBehaviourDoesNotAutomaticallyProveSubjectiveIntent :
  RepeatedOperationalEffectAutomaticallyProvesSubjectiveIntent → ⊥
systemBehaviourDoesNotAutomaticallyProveSubjectiveIntent ()

------------------------------------------------------------------------
-- POSIWID bridge: system-level operational description is available without
-- collapsing to mind-reading.
------------------------------------------------------------------------

observedOperationCanClassifySystemBehaviour :
  Operational.observedOperationMayClassifyWhatSystemDoes
    Operational.canonicalOperationalDescriptionBoundary ≡ true
observedOperationCanClassifySystemBehaviour = refl

observedOperationStillDoesNotProveIntent :
  Operational.observedOperationProvesSubjectiveIntent
    Operational.canonicalOperationalDescriptionBoundary ≡ false
observedOperationStillDoesNotProveIntent = refl
