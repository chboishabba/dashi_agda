module DASHI.Interop.GodsEyeViewDiagnosisDrivenActivistRollupExact where

------------------------------------------------------------------------
-- DIAGNOSIS-DRIVEN PUBLIC-INTEREST WORLD ROLLUP
--
-- This owner turns a world-state dashboard coordinate into a proof-search
-- surface.  A displayed concern is not a scalar moral score: it remains a
-- consumer-indexed evidence fibre with coverage, uncertainty, provenance,
-- unresolved causal distinctions, a first missing prerequisite and a least-
-- intrusive next-observation route.
--
-- SOURCE-DILIGENCE POLICY
-- Before a new empirical claim is promoted into the public-interest atlas, the
-- producer records an attempt to locate a primary/official source.  Secondary
-- sources remain admissible when necessary, but the failed/unavailable primary
-- search and the bounded role of the secondary source stay explicit.
--
-- Source packets below were checked 2026-09-08.  They are attribution anchors,
-- not automatic empirical or legal conclusions.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.GodsEyeViewPublicInterestWorldResidualExact as Public
import DASHI.Interop.GodsEyeViewActivistThreatAtlasExact as Atlas
import DASHI.Core.ArgumentResponseNonGeometricOppositeBidiExact as Response
import DASHI.Environment.LESSituatedSocioEcologicalHyperfabricExact as LES

------------------------------------------------------------------------
-- 1. Diagnosis-driven concern coordinate.
------------------------------------------------------------------------

record DiagnosedWorldConcern : Set where
  constructor diagnosed-world-concern
  field
    displayedCoordinate : Public.WorldConcernCoordinate
    concernReference : String
    propositionReference : String
    competingExplanationReferences : List String
    unresolvedCausalDistinctions : List String
    firstMissingPrerequisiteReference : String
    candidateProducerReferences : List String
    leastIntrusiveObservationReference : String
    proofSearchAdmissionReference : String
    sourceDiligenceReference : String
    affectedInterestReference : String
    remedyOrAccountabilityReference : String
    displayMayCollapseToSingleWrongnessScalar : Bool

open DiagnosedWorldConcern public

record DiagnosisDrivenWorldRollup : Set where
  constructor diagnosis-driven-world-rollup
  field
    rollupAt : String
    diagnosedCoordinates : List DiagnosedWorldConcern
    provenanceReference : String
    coverageReference : String
    uncertaintyReference : String
    ontologyDrilldownReference : String
    missingEvidenceReference : String
    contestabilityReference : String

------------------------------------------------------------------------
-- 2. Observation ethics is relational, not a geometric sign-flip.
------------------------------------------------------------------------

data AccountabilityObserverRole : Set where
  citizenObserver : AccountabilityObserverRole
  journalistObserver : AccountabilityObserverRole
  civilSocietyObserver : AccountabilityObserverRole
  researcherObserver : AccountabilityObserverRole
  corporationObserver : AccountabilityObserverRole
  lawEnforcementObserver : AccountabilityObserverRole
  intelligenceObserver : AccountabilityObserverRole
  immigrationEnforcementObserver : AccountabilityObserverRole
  foreignStateObserver : AccountabilityObserverRole

data AccountabilitySubjectRole : Set where
  publicOfficialSubject : AccountabilitySubjectRole
  policeOnDutySubject : AccountabilitySubjectRole
  publicInstitutionSubject : AccountabilitySubjectRole
  corporateFacilitySubject : AccountabilitySubjectRole
  pollutingFacilitySubject : AccountabilitySubjectRole
  publicEventSubject : AccountabilitySubjectRole
  ordinaryCitizenSubject : AccountabilitySubjectRole
  migrantOrDetaineeSubject : AccountabilitySubjectRole
  activistOrJournalistSubject : AccountabilitySubjectRole
  protectedWitnessSubject : AccountabilitySubjectRole

record ObservationRelation : Set where
  constructor observation-relation
  field
    observerRole : AccountabilityObserverRole
    subjectRole : AccountabilitySubjectRole
    purpose : Public.ObservationPurpose
    powerRelation : Public.PowerRelation
    publicDutyOrPowerHolderReference : String
    subjectVulnerabilityReference : String
    observerCoerciveCapacityReference : String
    retaliationRiskReference : String
    identityNecessityReference : String
    publicPlaceOrLawfulAccessReference : String
    minimisationReference : String
    publicationSafetyReference : String

-- Reversing observer and subject does not preserve the legal, ethical or power
-- geometry.  This is the observation analogue of the repository's existing
-- `opposite argument != geometric opposite` owner.
data ReversingObservationRolesPreservesEthics : Set where

reversingRolesIsNotGeometricEthicalOpposite :
  ReversingObservationRolesPreservesEthics → ⊥
reversingRolesIsNotGeometricEthicalOpposite ()

argumentResponseBoundaryAnchor : Response.ArgumentResponseGeometryBoundary
argumentResponseBoundaryAnchor = Response.canonicalArgumentResponseGeometryBoundary

------------------------------------------------------------------------
-- 3. Source diligence and fact admission.
------------------------------------------------------------------------

data SourceClass : Set where
  primaryOfficial : SourceClass
  primaryActorPublication : SourceClass
  courtFiling : SourceClass
  peerReviewedResearch : SourceClass
  officialSynthesis : SourceClass
  reputableSecondary : SourceClass
  advocacySecondary : SourceClass
  unresolvedSourceClass : SourceClass

record SourceDiligence : Set where
  constructor source-diligence
  field
    claimReference : String
    primarySearchAttempted : Bool
    primarySearchAttemptedIsTrue : primarySearchAttempted ≡ true
    primarySearchQueryOrMethodReference : String
    selectedSourceClass : SourceClass
    selectedSourceReference : String
    authorOrInstitutionReference : String
    exactSpanOrLocatorReference : String
    sourceDateOrRevisionReference : String
    secondaryFallbackReasonReference : String
    interpretationBoundaryReference : String
    contradictionSearchReference : String

record EmpiricalFactAdmission : Set where
  constructor empirical-fact-admission
  field
    claimReference : String
    diligence : SourceDiligence
    sameObjectReference : String
    temporalReference : String
    coverageReference : String
    uncertaintyReference : String
    provenanceReference : String
    sourceSupportsClaimReference : String
    interpretationDoesNotBecomeSourceReference : String
    downstreamAuthoritySeparateReference : String

------------------------------------------------------------------------
-- 4. Project 2025 primary-source attribution packet.
------------------------------------------------------------------------

record Project2025PrimaryPacket : Set where
  constructor project-2025-primary-packet
  field
    workTitle : String
    publisherFacilitator : String
    publicationReference : String
    editorsReference : String
    chapterAuthorsReference : String
    policyClaimMustNameChapterAndAuthor : Bool
    policyClaimMustNameChapterAndAuthorIsTrue :
      policyClaimMustNameChapterAndAuthor ≡ true
    implementationByLaterAdministrationRequiresSeparateEvidence : Bool
    implementationByLaterAdministrationRequiresSeparateEvidenceIsTrue :
      implementationByLaterAdministrationRequiresSeparateEvidence ≡ true

project2025PrimaryPacket : Project2025PrimaryPacket
project2025PrimaryPacket =
  project-2025-primary-packet
    "Mandate for Leadership: The Conservative Promise"
    "The Heritage Foundation / 2025 Presidential Transition Project"
    "Heritage primary PDF, ISBN 978-0-89195-174-2, 2023"
    "Paul Dans and Steven Groves"
    "Heritage's publication page lists 30 chapters and named authors; e.g. Ken Cuccinelli (DHS), Bernard L. McNamee (DOE), Mandy M. Gunasekara (EPA), Gene Hamilton (DOJ)"
    true refl
    true refl

------------------------------------------------------------------------
-- 5. Ozone/climate complexity packet.
------------------------------------------------------------------------

data OzoneClimateCoordinate : Set where
  stratosphericOzoneAmount : OzoneClimateCoordinate
  ozoneRecoveryTrend : OzoneClimateCoordinate
  ozoneDepletingHalocarbonForcing : OzoneClimateCoordinate
  ozoneLossRadiativeOffset : OzoneClimateCoordinate
  stratosphericTemperatureCirculation : OzoneClimateCoordinate
  tropicalSSTTeleconnection : OzoneClimateCoordinate
  troposphericOzonePollutionWarming : OzoneClimateCoordinate

record OzoneClimateSourcePacket : Set where
  constructor ozone-climate-source-packet
  field
    coordinates : List OzoneClimateCoordinate
    wmoReference : String
    recentPeerReviewedReference : String
    secondRecentPeerReviewedReference : String
    recoveryEqualsUniformClimateBenefit : Bool
    recoveryEqualsUniformClimateBenefitIsFalse :
      recoveryEqualsUniformClimateBenefit ≡ false
    ozoneLossEqualsNetCoolingFromHalocarbons : Bool
    ozoneLossEqualsNetCoolingFromHalocarbonsIsFalse :
      ozoneLossEqualsNetCoolingFromHalocarbons ≡ false
    localClimateEffectRequiresMechanismAndRegion : Bool
    localClimateEffectRequiresMechanismAndRegionIsTrue :
      localClimateEffectRequiresMechanismAndRegion ≡ true

ozoneClimateSourcePacket : OzoneClimateSourcePacket
ozoneClimateSourcePacket =
  ozone-climate-source-packet
    (stratosphericOzoneAmount
      ∷ ozoneRecoveryTrend
      ∷ ozoneDepletingHalocarbonForcing
      ∷ ozoneLossRadiativeOffset
      ∷ stratosphericTemperatureCirculation
      ∷ tropicalSSTTeleconnection
      ∷ troposphericOzonePollutionWarming
      ∷ [])
    "WMO Ozone and UV Bulletin No. 3 (2025): recovery trend plus continuing atmospheric variability/monitoring"
    "Dong et al., npj Climate and Atmospheric Science 8, 150 (2025): stratospheric ozone depletion and La Nina-like tropical SST pattern"
    "Nazarenko et al., npj Climate and Atmospheric Science 9, 106 (2026): OD-halocarbon net ERF remains extremely likely positive despite partial ozone-loss offset"
    false refl
    false refl
    true refl

------------------------------------------------------------------------
-- 6. Remote-sensing / photogrammetry accountability source packets.
------------------------------------------------------------------------

record RemoteSensingAccountabilityPacket : Set where
  constructor remote-sensing-accountability-packet
  field
    capabilityReference : String
    primaryTechnologyReference : String
    independentOrPeerReviewedReference : String
    intendedAccountabilityUseReference : String
    spatialResolutionReference : String
    temporalCoverageReference : String
    uncertaintyOrDetectionLimitReference : String
    individualIdentityResolutionRequired : Bool
    observationCreatesAccusation : Bool

carbonMapperPacket : RemoteSensingAccountabilityPacket
carbonMapperPacket =
  remote-sensing-accountability-packet
    "facility-scale methane/CO2 plume detection, quantification and public disclosure"
    "Carbon Mapper / NASA-JPL Tanager-1 imaging-spectrometer programme"
    "NASA first-plume release plus Carbon Mapper peer-reviewed-method references"
    "emissions mitigation and facility/operator accountability"
    "facility / plume scale; instrument-specific rather than person-identifying"
    "repeat satellite/aircraft observations"
    "detection threshold, wind and quantification uncertainty remain explicit"
    false
    false

ghanaDroneActivismPacket : RemoteSensingAccountabilityPacket
ghanaDroneActivismPacket =
  remote-sensing-accountability-packet
    "drone photogrammetry for environmental documentation of illegal-mining damage"
    "activist-operated UAV imagery / photogrammetry"
    "Dinko, Francisco & Malloy, Applied Geography 190 (2026), DOI 10.1016/j.apgeog.2026.103981"
    "counter-observation / public accountability for environmental degradation"
    "site-scale high-resolution 3D/orthophoto products"
    "mission/date dependent"
    "GCP/RTK/PPK geometry, occlusion and processing uncertainty remain explicit"
    false
    false

------------------------------------------------------------------------
-- 7. Civilian spatial-data repurposing / function-creep packet.
------------------------------------------------------------------------

record FunctionCreepSourcePacket : Set where
  constructor function-creep-source-packet
  field
    originalConsumerReference : String
    laterCapabilityReference : String
    primaryPartnershipReference : String
    dataLineageQuestionReference : String
    directDataSharingClaimReference : String
    militaryOrCoerciveUseCreatesOriginalUserConsent : Bool
    militaryOrCoerciveUseCreatesOriginalUserConsentIsFalse :
      militaryOrCoerciveUseCreatesOriginalUserConsent ≡ false

nianticVantorPacket : FunctionCreepSourcePacket
nianticVantorPacket =
  function-creep-source-packet
    "consumer/mobile spatial mapping ecosystem including Niantic spatial scans"
    "GPS-denied visual positioning for autonomous drones, vehicles and field assets"
    "Niantic Spatial + Vantor partnership announcements, 2025-12-16 and 2026-03-12"
    "which training observations, licences and consent surfaces feed later spatial-foundation capability must be separately audited"
    "the primary partnership announcement establishes the capability partnership, not a blanket claim that every Pokemon Go scan was directly transferred"
    false refl

------------------------------------------------------------------------
-- 8. Meta/Instagram legal allegation packet.
------------------------------------------------------------------------

data LegalClaimStatus : Set where
  pleadedAllegation : LegalClaimStatus
  adjudicatedFinding : LegalClaimStatus
  settlementWithoutAdmission : LegalClaimStatus
  officialEnforcementStatement : LegalClaimStatus
  unresolvedLegalStatus : LegalClaimStatus

record PlatformDesignLegalPacket : Set where
  constructor platform-design-legal-packet
  field
    defendantReference : String
    productReference : String
    primaryPleadingReference : String
    pleadedDesignTheoryReference : String
    currentProceedingReference : String
    claimStatus : LegalClaimStatus
    complaintAllegationEqualsAdjudicatedFact : Bool
    complaintAllegationEqualsAdjudicatedFactIsFalse :
      complaintAllegationEqualsAdjudicatedFact ≡ false

metaInstagramYouthPacket : PlatformDesignLegalPacket
metaInstagramYouthPacket =
  platform-design-legal-packet
    "Meta Platforms, Inc."
    "Instagram / Facebook youth-facing product design"
    "Multistate complaint, Case 4:23-cv-05448, filed 2023-10-24; New York AG hosts the complaint"
    "pleaded theories include allegedly addictive/manipulative engagement design and collection of data from children under 13 without parental consent"
    "2026 proceedings/settlement reporting must be source- and date-indexed separately from the original pleading"
    pleadedAllegation
    false refl

------------------------------------------------------------------------
-- 9. Detention and historical state-terror source packets remain distinct.
------------------------------------------------------------------------

record DetentionSourcePacket : Set where
  constructor detention-source-packet
  field
    caseReference : String
    sourceReference : String
    sourceClass : SourceClass
    boundedClaimReference : String
    exactPersonOrFacilityReference : String
    broaderInstitutionalInferenceRequiresAdditionalEvidence : Bool
    broaderInstitutionalInferenceRequiresAdditionalEvidenceIsTrue :
      broaderInstitutionalInferenceRequiresAdditionalEvidence ≡ true

cubanICEHungerStrikePacket : DetentionSourcePacket
cubanICEHungerStrikePacket =
  detention-source-packet
    "Cuban ICE detainee hunger-strike / force-feeding litigation, 2026"
    "contemporaneous court-linked reporting; primary court filing should be attached before legal promotion"
    reputableSecondary
    "reported judicial authorization for involuntary feeding of a named Cuban detainee at Montgomery ICE Processing Center"
    "named detainee/facility packet required before event-level WrongType or legality conclusion"
    true refl

argentinaClandestineDetentionPacket : DetentionSourcePacket
argentinaClandestineDetentionPacket =
  detention-source-packet
    "Argentina 1974-1983 clandestine detention / state-terror memory sites"
    "Argentina.gob.ar human-rights memory-site registry and clandestine-detention-centre map"
    primaryOfficial
    "official memory-site material documents clandestine detention and illegal confinement under the systematic state-terror apparatus of the dictatorship"
    "facility-specific records such as Olimpo/ESMA/La Perla remain separately addressable"
    true refl

------------------------------------------------------------------------
-- 10. LES cross-pollination: a public ecological surface cannot recover the
-- full planning distinction, and evidence adequacy still does not self-promote
-- to intervention authority.
------------------------------------------------------------------------

lesCoarseSurfaceCannotRecoverPlanningDistinction :
  {Recharted : Set} →
  (rechart : LES.FullCoarseObservation → Recharted) →
  (DASHI.Core.IntersectionalNonFactorability.FactorsThrough
    (λ state → rechart (LES.fullCoarseObservation state))
    LES.fullPlanningSignature) →
  ⊥
lesCoarseSurfaceCannotRecoverPlanningDistinction =
  LES.rechartingFullCoarseSummaryCannotRecoverFullPlanningSignature

------------------------------------------------------------------------
-- 11. Canonical boundary.
------------------------------------------------------------------------

record DiagnosisDrivenActivistRollupBoundary : Set where
  constructor diagnosis-driven-activist-rollup-boundary
  field
    worldConcernCoordinateIsGlobalWrongnessScore : Bool
    worldConcernCoordinateIsGlobalWrongnessScoreIsFalse :
      worldConcernCoordinateIsGlobalWrongnessScore ≡ false
    citizenWatchingPublicPowerEqualsStateWatchingCitizen : Bool
    citizenWatchingPublicPowerEqualsStateWatchingCitizenIsFalse :
      citizenWatchingPublicPowerEqualsStateWatchingCitizen ≡ false
    reversingObserverRolesPreservesEthics : Bool
    reversingObserverRolesPreservesEthicsIsFalse :
      reversingObserverRolesPreservesEthics ≡ false
    newEmpiricalFactMaySkipPrimarySourceSearch : Bool
    newEmpiricalFactMaySkipPrimarySourceSearchIsFalse :
      newEmpiricalFactMaySkipPrimarySourceSearch ≡ false
    project2025LabelAloneIsSufficientAttribution : Bool
    project2025LabelAloneIsSufficientAttributionIsFalse :
      project2025LabelAloneIsSufficientAttribution ≡ false
    complaintAllegationIsAutomaticallyAdjudicatedFact : Bool
    complaintAllegationIsAutomaticallyAdjudicatedFactIsFalse :
      complaintAllegationIsAutomaticallyAdjudicatedFact ≡ false
    remoteSensingObservationCreatesAccusation : Bool
    remoteSensingObservationCreatesAccusationIsFalse :
      remoteSensingObservationCreatesAccusation ≡ false
    lessIntrusiveEvidenceQuestionMustRemainLive : Bool
    lessIntrusiveEvidenceQuestionMustRemainLiveIsTrue :
      lessIntrusiveEvidenceQuestionMustRemainLive ≡ true
    ontologyDrilldownMustRemainAvailable : Bool
    ontologyDrilldownMustRemainAvailableIsTrue :
      ontologyDrilldownMustRemainAvailable ≡ true

canonicalDiagnosisDrivenActivistRollupBoundary :
  DiagnosisDrivenActivistRollupBoundary
canonicalDiagnosisDrivenActivistRollupBoundary =
  diagnosis-driven-activist-rollup-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
