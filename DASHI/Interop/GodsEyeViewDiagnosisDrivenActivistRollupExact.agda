module DASHI.Interop.GodsEyeViewDiagnosisDrivenActivistRollupExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.GodsEyeViewPublicInterestWorldResidualExact as Public
import DASHI.Interop.GodsEyeViewActivistThreatAtlasExact as Atlas
import DASHI.Core.ArgumentResponseNonGeometricOppositeBidiExact as Response
import DASHI.Environment.LESSituatedSocioEcologicalHyperfabricExact as LES
import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- Diagnosis-driven public-interest rollup.
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
-- Observer-role asymmetry: reversing the gaze is not a geometric antipode.
------------------------------------------------------------------------

data AccountabilityObserverRole : Set where
  citizenObserver journalistObserver civilSocietyObserver researcherObserver : AccountabilityObserverRole
  corporationObserver lawEnforcementObserver intelligenceObserver : AccountabilityObserverRole
  immigrationEnforcementObserver foreignStateObserver : AccountabilityObserverRole

data AccountabilitySubjectRole : Set where
  publicOfficialSubject policeOnDutySubject publicInstitutionSubject : AccountabilitySubjectRole
  corporateFacilitySubject pollutingFacilitySubject publicEventSubject : AccountabilitySubjectRole
  ordinaryCitizenSubject migrantOrDetaineeSubject activistOrJournalistSubject : AccountabilitySubjectRole
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

data ReversingObservationRolesPreservesEthics : Set where
reversingRolesIsNotGeometricEthicalOpposite : ReversingObservationRolesPreservesEthics → ⊥
reversingRolesIsNotGeometricEthicalOpposite ()

argumentResponseBoundaryAnchor : Response.ArgumentResponseGeometryBoundary
argumentResponseBoundaryAnchor = Response.canonicalArgumentResponseGeometryBoundary

------------------------------------------------------------------------
-- Source diligence: primary-source search is itself part of fact admission.
------------------------------------------------------------------------

data SourceClass : Set where
  primaryOfficial primaryActorPublication courtFiling peerReviewedResearch : SourceClass
  officialSynthesis reputableSecondary advocacySecondary unresolvedSourceClass : SourceClass

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
-- Project 2025 primary attribution.
------------------------------------------------------------------------

record Project2025PrimaryPacket : Set where
  constructor project-2025-primary-packet
  field
    workTitle publisherFacilitator publicationReference editorsReference chapterAuthorsReference : String
    policyClaimMustNameChapterAndAuthor : Bool
    policyClaimMustNameChapterAndAuthorIsTrue : policyClaimMustNameChapterAndAuthor ≡ true
    laterImplementationRequiresSeparateEvidence : Bool
    laterImplementationRequiresSeparateEvidenceIsTrue : laterImplementationRequiresSeparateEvidence ≡ true

project2025PrimaryPacket : Project2025PrimaryPacket
project2025PrimaryPacket = project-2025-primary-packet
  "Mandate for Leadership: The Conservative Promise"
  "The Heritage Foundation / 2025 Presidential Transition Project"
  "Heritage primary PDF, ISBN 978-0-89195-174-2, 2023"
  "Paul Dans and Steven Groves"
  "Heritage lists 30 chapter authors; examples: Ken Cuccinelli DHS, Bernard L. McNamee DOE, Mandy M. Gunasekara EPA, Gene Hamilton DOJ"
  true refl true refl

------------------------------------------------------------------------
-- Ozone / climate is a multi-coordinate coupling, not a one-bit good/bad axis.
------------------------------------------------------------------------

data OzoneClimateCoordinate : Set where
  stratosphericOzoneAmount ozoneRecoveryTrend ozoneDepletingHalocarbonForcing : OzoneClimateCoordinate
  ozoneLossRadiativeOffset stratosphericTemperatureCirculation : OzoneClimateCoordinate
  tropicalSSTTeleconnection troposphericOzonePollutionWarming : OzoneClimateCoordinate

record OzoneClimateSourcePacket : Set where
  constructor ozone-climate-source-packet
  field
    coordinates : List OzoneClimateCoordinate
    wmoReference recentPeerReviewedReference secondRecentPeerReviewedReference : String
    recoveryEqualsUniformClimateBenefit : Bool
    recoveryEqualsUniformClimateBenefitIsFalse : recoveryEqualsUniformClimateBenefit ≡ false
    ozoneLossEqualsNetCoolingFromHalocarbons : Bool
    ozoneLossEqualsNetCoolingFromHalocarbonsIsFalse : ozoneLossEqualsNetCoolingFromHalocarbons ≡ false
    localClimateEffectRequiresMechanismAndRegion : Bool
    localClimateEffectRequiresMechanismAndRegionIsTrue : localClimateEffectRequiresMechanismAndRegion ≡ true

ozoneClimateSourcePacket : OzoneClimateSourcePacket
ozoneClimateSourcePacket = ozone-climate-source-packet
  (stratosphericOzoneAmount ∷ ozoneRecoveryTrend ∷ ozoneDepletingHalocarbonForcing ∷ ozoneLossRadiativeOffset ∷ stratosphericTemperatureCirculation ∷ tropicalSSTTeleconnection ∷ troposphericOzonePollutionWarming ∷ [])
  "WMO Ozone and UV Bulletin No. 3 (2025)"
  "Dong et al., npj Climate and Atmospheric Science 8, 150 (2025): ozone depletion and La Nina-like tropical SST pattern"
  "Nazarenko et al., npj Climate and Atmospheric Science 9, 106 (2026): OD-halocarbon net ERF remains positive despite partial ozone-loss offset"
  false refl false refl true refl

------------------------------------------------------------------------
-- Remote sensing / photogrammetry accountability packets.
------------------------------------------------------------------------

record RemoteSensingAccountabilityPacket : Set where
  constructor remote-sensing-accountability-packet
  field
    capabilityReference primaryTechnologyReference independentOrPeerReviewedReference : String
    intendedAccountabilityUseReference spatialResolutionReference temporalCoverageReference : String
    uncertaintyOrDetectionLimitReference : String
    individualIdentityResolutionRequired observationCreatesAccusation : Bool

carbonMapperPacket : RemoteSensingAccountabilityPacket
carbonMapperPacket = remote-sensing-accountability-packet
  "facility-scale methane/CO2 plume detection and quantification"
  "Carbon Mapper / NASA-JPL Tanager-1 imaging spectrometer"
  "NASA first-plume release plus Carbon Mapper scientific-method references"
  "emissions mitigation and facility/operator accountability"
  "facility/plume scale" "repeat satellite/aircraft observations"
  "detection threshold, wind and quantification uncertainty remain explicit"
  false false

ghanaDroneActivismPacket : RemoteSensingAccountabilityPacket
ghanaDroneActivismPacket = remote-sensing-accountability-packet
  "drone photogrammetry documenting illegal-mining environmental damage"
  "activist-operated UAV imagery / photogrammetry"
  "Dinko, Francisco & Malloy, Applied Geography 190 (2026), DOI 10.1016/j.apgeog.2026.103981"
  "counter-observation / democratic environmental accountability"
  "site-scale high-resolution 3D/orthophoto products" "mission/date dependent"
  "GCP/RTK/PPK geometry, occlusion and processing uncertainty remain explicit"
  false false

------------------------------------------------------------------------
-- Civilian spatial-data function creep / military repurposing.
------------------------------------------------------------------------

record FunctionCreepSourcePacket : Set where
  constructor function-creep-source-packet
  field
    originalConsumerReference laterCapabilityReference primaryPartnershipReference : String
    dataLineageQuestionReference directDataSharingClaimReference : String
    laterCoerciveUseCreatesOriginalUserConsent : Bool
    laterCoerciveUseCreatesOriginalUserConsentIsFalse : laterCoerciveUseCreatesOriginalUserConsent ≡ false

nianticVantorPacket : FunctionCreepSourcePacket
nianticVantorPacket = function-creep-source-packet
  "consumer/mobile spatial mapping ecosystem including Niantic spatial scans"
  "GPS-denied visual positioning for autonomous drones, vehicles and field assets"
  "Niantic Spatial + Vantor primary partnership announcements, 2025-12-16 and 2026-03-12"
  "training-observation lineage, licences and consent require a separate audit"
  "the partnership proves the capability partnership, not that every Pokemon Go scan was directly transferred"
  false refl

------------------------------------------------------------------------
-- Platform-design legal packet: allegation != adjudicated fact.
------------------------------------------------------------------------

data LegalClaimStatus : Set where
  pleadedAllegation adjudicatedFinding settlementStatus officialEnforcementStatement unresolvedLegalStatus : LegalClaimStatus

record PlatformDesignLegalPacket : Set where
  constructor platform-design-legal-packet
  field
    defendantReference productReference primaryPleadingReference : String
    pleadedDesignTheoryReference currentProceedingReference : String
    claimStatus : LegalClaimStatus
    complaintAllegationEqualsAdjudicatedFact : Bool
    complaintAllegationEqualsAdjudicatedFactIsFalse : complaintAllegationEqualsAdjudicatedFact ≡ false

metaInstagramYouthPacket : PlatformDesignLegalPacket
metaInstagramYouthPacket = platform-design-legal-packet
  "Meta Platforms, Inc." "Instagram / Facebook youth-facing product design"
  "Multistate complaint, Case 4:23-cv-05448, filed 2023-10-24; hosted by New York Attorney General"
  "pleaded addictive/manipulative engagement-design and under-13 data-collection theories"
  "2026 proceeding/settlement state must be separately date-indexed from the original pleading"
  pleadedAllegation false refl

------------------------------------------------------------------------
-- Detention/state-terror packets: source facts stay case/facility specific.
------------------------------------------------------------------------

record DetentionSourcePacket : Set where
  constructor detention-source-packet
  field
    caseReference sourceReference : String
    sourceClass : SourceClass
    boundedClaimReference exactPersonOrFacilityReference : String
    broaderInstitutionalInferenceRequiresAdditionalEvidence : Bool
    broaderInstitutionalInferenceRequiresAdditionalEvidenceIsTrue : broaderInstitutionalInferenceRequiresAdditionalEvidence ≡ true

cubanICEHungerStrikePacket : DetentionSourcePacket
cubanICEHungerStrikePacket = detention-source-packet
  "Cuban ICE detainee hunger-strike / force-feeding litigation, 2026"
  "contemporaneous court-linked reporting; primary court filing remains required before legal promotion"
  reputableSecondary
  "reported judicial authorization for involuntary feeding of a Cuban detainee at Montgomery ICE Processing Center"
  "named detainee/facility packet required before event-level WrongType or legality conclusion"
  true refl

argentinaClandestineDetentionPacket : DetentionSourcePacket
argentinaClandestineDetentionPacket = detention-source-packet
  "Argentina 1974-1983 clandestine detention / state-terror memory sites"
  "Argentina.gob.ar human-rights memory-site registry and clandestine-detention-centre map"
  primaryOfficial
  "official memory-site material documents clandestine detention and illegal confinement under the dictatorship's state-terror apparatus"
  "facility records such as Olimpo/ESMA/La Perla remain separately addressable"
  true refl

------------------------------------------------------------------------
-- LES: a coarse public ecological surface cannot recover the full planning
-- signature; recharting cannot recreate erased history/relation/provenance/
-- justice coordinates.
------------------------------------------------------------------------

lesCoarseSurfaceCannotRecoverPlanningDistinction :
  {Recharted : Set} →
  (rechart : LES.FullCoarseObservation → Recharted) →
  INF.FactorsThrough (λ state → rechart (LES.fullCoarseObservation state)) LES.fullPlanningSignature →
  ⊥
lesCoarseSurfaceCannotRecoverPlanningDistinction = LES.rechartingFullCoarseSummaryCannotRecoverFullPlanningSignature

------------------------------------------------------------------------
-- Canonical boundaries.
------------------------------------------------------------------------

record DiagnosisDrivenActivistRollupBoundary : Set where
  constructor diagnosis-driven-activist-rollup-boundary
  field
    worldConcernCoordinateIsGlobalWrongnessScore : Bool
    worldConcernCoordinateIsGlobalWrongnessScoreIsFalse : worldConcernCoordinateIsGlobalWrongnessScore ≡ false
    citizenWatchingPublicPowerEqualsStateWatchingCitizen : Bool
    citizenWatchingPublicPowerEqualsStateWatchingCitizenIsFalse : citizenWatchingPublicPowerEqualsStateWatchingCitizen ≡ false
    reversingObserverRolesPreservesEthics : Bool
    reversingObserverRolesPreservesEthicsIsFalse : reversingObserverRolesPreservesEthics ≡ false
    newEmpiricalFactMaySkipPrimarySourceSearch : Bool
    newEmpiricalFactMaySkipPrimarySourceSearchIsFalse : newEmpiricalFactMaySkipPrimarySourceSearch ≡ false
    project2025LabelAloneIsSufficientAttribution : Bool
    project2025LabelAloneIsSufficientAttributionIsFalse : project2025LabelAloneIsSufficientAttribution ≡ false
    complaintAllegationIsAutomaticallyAdjudicatedFact : Bool
    complaintAllegationIsAutomaticallyAdjudicatedFactIsFalse : complaintAllegationIsAutomaticallyAdjudicatedFact ≡ false
    remoteSensingObservationCreatesAccusation : Bool
    remoteSensingObservationCreatesAccusationIsFalse : remoteSensingObservationCreatesAccusation ≡ false
    lessIntrusiveEvidenceQuestionMustRemainLive : Bool
    lessIntrusiveEvidenceQuestionMustRemainLiveIsTrue : lessIntrusiveEvidenceQuestionMustRemainLive ≡ true
    ontologyDrilldownMustRemainAvailable : Bool
    ontologyDrilldownMustRemainAvailableIsTrue : ontologyDrilldownMustRemainAvailable ≡ true

canonicalDiagnosisDrivenActivistRollupBoundary : DiagnosisDrivenActivistRollupBoundary
canonicalDiagnosisDrivenActivistRollupBoundary = diagnosis-driven-activist-rollup-boundary
  false refl false refl false refl false refl false refl false refl false refl true refl true refl
