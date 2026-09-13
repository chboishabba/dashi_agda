module DASHI.Interop.GodsEyeViewPublicInterestWorldResidualExact where

------------------------------------------------------------------------
-- GOD'S EYE VIEW x PUBLIC-INTEREST WORLD RESIDUAL
--
-- This owner turns the proof-carrying world ontology into an executable
-- observation-selection seam.  The aim is not maximal surveillance coverage;
-- it is the least intrusive admissible observation that materially reduces a
-- declared consumer's unresolved world/query residual.
--
-- SOURCE / METHODOLOGICAL CALIBRATION
-- Audre Lorde, "The Master's Tools Will Never Dismantle the Master's House",
-- remarks delivered 1979; collected in Sister Outsider, Crossing Press, 1984.
-- The repository already owns this as methodological tension in
-- DASHI.Core.FormalisationCompatibilityExact.  This module does not claim that
-- using observation/fusion tools for public-interest work resolves that tension.
--
-- Positive application calibration:
-- UNEP International Methane Emissions Observatory, Methane Alert and Response
-- System (MARS): satellite detection -> attribution -> notification ->
-- mitigation/tracking.  This is application inspiration only; UNEP does not own
-- the DASHI ontology, governance policy, or proof-search semantics below.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.GodsEyeViewProofCarryingWorldOntologyExact as GEV
import DASHI.Core.FormalisationCompatibilityExact as Compatibility
import DASHI.Interop.SensibLawOntologyTopology as Sensib
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as ProofSearch

------------------------------------------------------------------------
-- 1. Observation purpose, scale and power relation are first-class.
------------------------------------------------------------------------

data ObservationPurpose : Set where
  publicInterestJournalism : ObservationPurpose
  institutionalAccountability : ObservationPurpose
  environmentalAccountability : ObservationPurpose
  humanitarianAssessment : ObservationPurpose
  scientificMeasurement : ObservationPurpose
  legalEvidenceAcquisition : ObservationPurpose
  commercialAnalytics : ObservationPurpose
  lawEnforcementInvestigation : ObservationPurpose
  immigrationEnforcement : ObservationPurpose
  unspecifiedPurpose : ObservationPurpose


data SubjectScale : Set where
  planetary : SubjectScale
  regional : SubjectScale
  facilityScale : SubjectScale
  eventScale : SubjectScale
  organisationScale : SubjectScale
  individualScale : SubjectScale


data PowerRelation : Set where
  publicObservesPublicInstitution : PowerRelation
  publicObservesCorporateFacility : PowerRelation
  journalistObservesPowerHolder : PowerRelation
  institutionObservesInstitution : PowerRelation
  institutionObservesPublic : PowerRelation
  stateObservesIndividual : PowerRelation
  corporationObservesIndividual : PowerRelation
  peerObservation : PowerRelation
  unresolvedPowerRelation : PowerRelation

------------------------------------------------------------------------
-- 2. Governance risk is an upstream system/deployment audit.
--
-- This is distinct from applying a concrete SensibLaw WrongType to a person or
-- event.  The latter remains downstream of evidence, applicability and source
-- authority.  Here we can nevertheless flag architectural/deployment risk
-- before a particular abuse is proven.
------------------------------------------------------------------------

data GovernanceRisk : Set where
  privacyRisk : GovernanceRisk
  nonDominationRisk : GovernanceRisk
  chillingEffectRisk : GovernanceRisk
  discriminatorySurveillanceRisk : GovernanceRisk
  functionCreepRisk : GovernanceRisk
  persistentObservabilityRisk : GovernanceRisk
  identityResolutionRisk : GovernanceRisk
  crossDatasetLinkageRisk : GovernanceRisk
  enforcementCouplingRisk : GovernanceRisk
  informationAsymmetryRisk : GovernanceRisk
  vulnerablePopulationBurden : GovernanceRisk

record GovernanceRiskAssessment : Set where
  constructor governance-risk-assessment
  field
    assessedSystemReference : String
    purpose : ObservationPurpose
    subjectScale : SubjectScale
    powerRelation : PowerRelation
    candidateRisks : List GovernanceRisk
    retentionReference : String
    identityResolutionReference : String
    linkageReference : String
    purposeLimitationReference : String
    accessControlReference : String
    contestabilityReference : String
    enforcementCouplingReference : String
    affectedPopulationBurdenReference : String
    assessmentEvidenceReference : String

open GovernanceRiskAssessment public

------------------------------------------------------------------------
-- 3. Concrete event WrongType remains downstream.
------------------------------------------------------------------------

record ConcreteWrongTypeGate : Set where
  constructor concrete-wrongtype-gate
  field
    worldState : GEV.ResolvedWorldState
    wrongTypeInterpretationReference : String
    evidenceReference : String
    applicabilityReference : String
    sourceAuthorityReference : String

-- Merely seeing/rendering a subject cannot construct the concrete gate.
data VisibilityCreatesConcreteWrongType : Set where

visibilityDoesNotCreateConcreteWrongType :
  VisibilityCreatesConcreteWrongType → ⊥
visibilityDoesNotCreateConcreteWrongType ()

------------------------------------------------------------------------
-- 4. Consumer-scoped unresolved world residual.
------------------------------------------------------------------------

record WorldQueryResidual : Set where
  constructor world-query-residual
  field
    queryReference : String
    selectedObject : GEV.WorldObjectRef
    consumer : GEV.WorldConsumer
    currentState : GEV.ResolvedWorldState
    currentObservationReferences : List Sensib.StableId
    coverageReference : String
    unresolvedDistinctions : List String
    missingPrerequisiteReference : String
    candidateProducerReferences : List String
    authorityRequirementReference : String
    privacyBurdenReference : String
    nonDominationBurdenReference : String
    publicInterestReference : String

open WorldQueryResidual public

------------------------------------------------------------------------
-- 5. Candidate next observation.
--
-- Information gain is deliberately represented by a proof/reference rather
-- than an ungrounded scalar here.  A later quantitative owner may instantiate
-- a calibrated score without weakening the governance requirements.
------------------------------------------------------------------------

record CandidateObservation : Set where
  constructor candidate-observation
  field
    residual : WorldQueryResidual
    proposedCoordinate : GEV.ObservationCoordinate
    proposedPurpose : ObservationPurpose
    proposedSubjectScale : SubjectScale
    proposedPowerRelation : PowerRelation
    expectedResidualReductionReference : String
    sourceAuthorityReference : String
    acquisitionAuthorityReference : String
    costReference : String
    privacyBurdenReference : String
    nonDominationBurdenReference : String
    lessIntrusiveAlternativeAuditReference : String
    governanceRiskAssessment : GovernanceRiskAssessment

open CandidateObservation public

------------------------------------------------------------------------
-- 6. Observation least privilege.
--
-- This is the observation analogue of proof-search least privilege:
-- acquiring more data is not progress unless it pays the declared residual,
-- has the required authority, and no less intrusive admitted candidate pays the
-- same prerequisite under the selected policy.
------------------------------------------------------------------------

record ObservationLeastPrivilegeAdmission : Set where
  constructor observation-least-privilege-admission
  field
    candidate : CandidateObservation
    proofSearchAdmission : ProofSearch.RouteAdmission
    exactConsumerResidualReference : String
    candidatePaysMissingPrerequisiteReference : String
    acquisitionIsAuthorisedReference : String
    provenanceWillSurviveReference : String
    coverageWillRemainExplicitReference : String
    lessIntrusiveEquivalentRejectedReference : String
    privacyBurdenAcceptedReference : String
    nonDominationBurdenAcceptedReference : String
    downstreamActionAuthoritySeparateReference : String

open ObservationLeastPrivilegeAdmission public

------------------------------------------------------------------------
-- 7. Positive planetary/public-interest observation case.
--
-- Facility/regional/planetary environmental sensing is not silently identified
-- with individual surveillance.  It still needs provenance, coverage,
-- uncertainty and downstream-action separation, but its subject/power/burden
-- coordinates can be categorically different.
------------------------------------------------------------------------

record PlanetaryAccountabilityObservation : Set where
  constructor planetary-accountability-observation
  field
    observation : GEV.ObservationReceipt
    environmentalPhenomenonReference : String
    geographicScaleReference : String
    sourceInstrumentReference : String
    detectionLimitReference : String
    uncertaintyReference : String
    attributionToFacilityOrRegionReference : String
    publicDataReference : String
    mitigationOrAccountabilityConsumerReference : String
    noIndividualIdentityResolutionReference : String

open PlanetaryAccountabilityObservation public

------------------------------------------------------------------------
-- 8. World-state rollup is a dashboard projection, not a moral oracle.
------------------------------------------------------------------------

data WorldConcernAxis : Set where
  climateEmissions : WorldConcernAxis
  landAndHabitatLoss : WorldConcernAxis
  humanitarianStress : WorldConcernAxis
  conflictAndViolence : WorldConcernAxis
  institutionalAccountabilityAxis : WorldConcernAxis
  informationIntegrity : WorldConcernAxis
  publicHealthAndSafety : WorldConcernAxis

record WorldConcernCoordinate : Set where
  constructor world-concern-coordinate
  field
    axis : WorldConcernAxis
    stateReference : String
    evidenceReferences : List Sensib.StableId
    coverageReference : String
    uncertaintyReference : String
    temporalReference : String
    consumerReference : String

record WorldStateRollup : Set where
  constructor world-state-rollup
  field
    rollupAt : String
    coordinates : List WorldConcernCoordinate
    provenanceReference : String
    aggregationPolicyReference : String
    missingCoverageReference : String
    contestabilityReference : String

------------------------------------------------------------------------
-- 9. Lorde methodological-tension anchor.
------------------------------------------------------------------------

lordeMethodologicalTension : Compatibility.CompatibilityAssessment
lordeMethodologicalTension = Compatibility.canonicalMethodologicalTension

------------------------------------------------------------------------
-- 10. Canonical ethics / authority boundary.
------------------------------------------------------------------------

record PublicInterestWorldResidualBoundary : Set where
  constructor public-interest-world-residual-boundary
  field
    systemRiskAuditEqualsConcreteWrongTypeFinding : Bool
    systemRiskAuditEqualsConcreteWrongTypeFindingIsFalse :
      systemRiskAuditEqualsConcreteWrongTypeFinding ≡ false

    publicInterestPurposeAutomaticallyAuthorisesObservation : Bool
    publicInterestPurposeAutomaticallyAuthorisesObservationIsFalse :
      publicInterestPurposeAutomaticallyAuthorisesObservation ≡ false

    moreCoverageAutomaticallyImprovesEthics : Bool
    moreCoverageAutomaticallyImprovesEthicsIsFalse :
      moreCoverageAutomaticallyImprovesEthics ≡ false

    planetarySensingEqualsIndividualSurveillance : Bool
    planetarySensingEqualsIndividualSurveillanceIsFalse :
      planetarySensingEqualsIndividualSurveillance ≡ false

    observationAuthorityEqualsInterventionAuthority : Bool
    observationAuthorityEqualsInterventionAuthorityIsFalse :
      observationAuthorityEqualsInterventionAuthority ≡ false

    worldRollupIsCompleteMoralTruth : Bool
    worldRollupIsCompleteMoralTruthIsFalse :
      worldRollupIsCompleteMoralTruth ≡ false

    unresolvedCoverageMustRemainVisible : Bool
    unresolvedCoverageMustRemainVisibleIsTrue :
      unresolvedCoverageMustRemainVisible ≡ true

    leastIntrusiveEquivalentMustBeAudited : Bool
    leastIntrusiveEquivalentMustBeAuditedIsTrue :
      leastIntrusiveEquivalentMustBeAudited ≡ true

    methodologicalTensionMayRemainWhileConstructionProceeds : Bool
    methodologicalTensionMayRemainWhileConstructionProceedsIsTrue :
      methodologicalTensionMayRemainWhileConstructionProceeds ≡ true

canonicalPublicInterestWorldResidualBoundary : PublicInterestWorldResidualBoundary
canonicalPublicInterestWorldResidualBoundary =
  public-interest-world-residual-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
