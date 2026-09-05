module DASHI.Physics.Nuclear.LeBlancFissionSurfacePowerICBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Core.TechnicalDependencyHypergraphExact as Hypergraph

------------------------------------------------------------------------
-- LEBLANC / NASA FISSION-SURFACE-POWER I&C BIDI OWNER
--
-- Primary source:
-- NASA 40 kW Fission Surface Power I&C Technology Development Path,
-- Fission Surface Power Technology Maturation Webinar Series, 26 Aug 2025,
-- NASA NTRS document 20250008475.
-- Named authors include Joshua LeBlanc, NASA Marshall Space Flight Center.
-- NASA FICS Executive Committee slide identifies Joshua LeBlanc as NASA SNP
-- I&C TechMat Team Lead.
--
-- This file formalises the engineering dependency structure actually present
-- in the presentation.  Notional environmental values remain notional and are
-- not promoted into universal FSP requirements.
------------------------------------------------------------------------

data FSPSystemRegion : Set where
  PMAD
  coldSideHeatExchanger
  radiator
  turbineCompressor
  hotSideHeatExchanger
  controlDrums
  inCore
  : FSPSystemRegion

data ICSensorKind : Set where
  radiationDetector
  temperatureSensor
  pressureSensor
  flowSensor
  strainSensor
  speedSensor
  positionSensor
  vibrationSensor
  tiltSensor
  potentiometer
  hydrogenSensor
  electromagneticSensor
  : ICSensorKind

data ICFunction : Set where
  measureState
  selfDiagnosis
  faultDetection
  communicateState
  automatedFaultResponse
  processControl
  reliabilityValidation
  gapAnalysis
  technologyRoadmapping
  : ICFunction

data EnvironmentalAxis : Set where
  temperature
  neutronFlux
  neutronFluence
  gammaDose
  pressure
  massFlow
  vibration
  vacuum
  : EnvironmentalAxis

record SourceRange : Set where
  constructor source-range
  field
    axis : EnvironmentalAxis
    sourceNotationLower : String
    sourceNotationUpper : String
    unit : String
    location : FSPSystemRegion
    isNotional : Bool
    isNotionalIsTrue : isNotional ≡ true

open SourceRange public

------------------------------------------------------------------------
-- Selected source-exact notional coordinates from the 40 kW draft path.
------------------------------------------------------------------------

inCoreTemperature : SourceRange
inCoreTemperature =
  source-range temperature ">1200" ">1200" "K" inCore true refl

inCoreNeutronFlux : SourceRange
inCoreNeutronFlux =
  source-range neutronFlux "10^12" "10^12" "n cm^-2 s^-1" inCore true refl

inCoreNeutronFluence : SourceRange
inCoreNeutronFluence =
  source-range neutronFluence "10^21" "10^21" "n cm^-2" inCore true refl

inCoreGammaDose : SourceRange
inCoreGammaDose =
  source-range gammaDose "8E10" "8E10" "krad" inCore true refl

pressureSensorPressureRange : SourceRange
pressureSensorPressureRange =
  source-range pressure "900" "1500" "kPa" inCore true refl

flowSensorMassFlowRange : SourceRange
flowSensorMassFlowRange =
  source-range massFlow "0.05" "0.5" "kg/s" inCore true refl

------------------------------------------------------------------------
-- NASA's engineering logic is a dependency chain rather than a scalar score:
--
--   mission environment
--      -> measurement requirements
--      -> candidate sensor technology
--      -> state-of-the-art comparison
--      -> gaps / barriers / risks
--      -> maturation roadmap
--      -> integrated diagnostics/control
--      -> autonomous response to off-normal conditions.
------------------------------------------------------------------------

record ICRequirementHypervoxel : Set where
  constructor ic-requirement-hypervoxel
  field
    region : FSPSystemRegion
    sensor : ICSensorKind
    environmentalEnvelope : List SourceRange
    requiredFunctions : List ICFunction
    tenYearNoMaintenanceContext : Bool
    tenYearNoMaintenanceContextIsTrue :
      tenYearNoMaintenanceContext ≡ true
    sourceReference : String

open ICRequirementHypervoxel public

record ICMaturationEdge : Set where
  constructor ic-maturation-edge
  field
    fromStage : String
    toStage : String
    producer : String
    evidenceObject : String
    reversesTo : String

open ICMaturationEdge public

referenceSystemToRequirements : ICMaturationEdge
referenceSystemToRequirements =
  ic-maturation-edge
    "reference system"
    "high-level sensor requirements"
    "mission/system decomposition"
    "FICS Working Group activity list"
    "acquire reference-system definition before promoting a requirement"

requirementsToGap : ICMaturationEdge
requirementsToGap =
  ic-maturation-edge
    "requirements"
    "gaps / barriers / risks"
    "SOA-to-requirement comparison"
    "FSP-CINDI plus working-group comparison"
    "acquire both requirement and state-of-the-art receipt"

gapToRoadmap : ICMaturationEdge
gapToRoadmap =
  ic-maturation-edge
    "gaps / barriers / risks"
    "technology development roadmap"
    "maturation planning"
    "draft NASA I&C Technology Development Path"
    "roadmap item must reverse to an identified gap"

sensorToAutonomousResponse : ICMaturationEdge
sensorToAutonomousResponse =
  ic-maturation-edge
    "smart sensor + diagnostic state"
    "automated off-normal response"
    "control software integrated with fault detection"
    "NASA slide: modern control/diagnostic software integrated with smart sensors and fault detection"
    "observed automation does not identify unique sensor or diagnostic algorithm"

------------------------------------------------------------------------
-- BIDI boundaries.
------------------------------------------------------------------------

record FSPICBidiBoundary : Set where
  constructor fsp-ic-bidi-boundary
  field
    harshEnvironmentAloneSelectsUniqueSensorTechnology : Bool
    harshEnvironmentAloneSelectsUniqueSensorTechnologyIsFalse :
      harshEnvironmentAloneSelectsUniqueSensorTechnology ≡ false

    databaseRankingIsEquivalentToFlightQualification : Bool
    databaseRankingIsEquivalentToFlightQualificationIsFalse :
      databaseRankingIsEquivalentToFlightQualification ≡ false

    notionalRangeIsUniversalMissionRequirement : Bool
    notionalRangeIsUniversalMissionRequirementIsFalse :
      notionalRangeIsUniversalMissionRequirement ≡ false

    componentReliabilityImpliesSystemReliability : Bool
    componentReliabilityImpliesSystemReliabilityIsFalse :
      componentReliabilityImpliesSystemReliability ≡ false

    redundancyAloneProvesZeroFailure : Bool
    redundancyAloneProvesZeroFailureIsFalse :
      redundancyAloneProvesZeroFailure ≡ false

    faultDetectionUniquelyDeterminesCorrectiveAction : Bool
    faultDetectionUniquelyDeterminesCorrectiveActionIsFalse :
      faultDetectionUniquelyDeterminesCorrectiveAction ≡ false

    autonomousControlRequiresObservableDiagnosticState : Bool
    autonomousControlRequiresObservableDiagnosticStateIsTrue :
      autonomousControlRequiresObservableDiagnosticState ≡ true

canonicalFSPICBidiBoundary : FSPICBidiBoundary
canonicalFSPICBidiBoundary =
  fsp-ic-bidi-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl

------------------------------------------------------------------------
-- Reverse acquisition router.
------------------------------------------------------------------------

data FSPICReverseTarget : Set where
  acquireReferenceSystem
  acquireEnvironmentalEnvelope
  acquireMeasurementRequirement
  acquireCandidateSensor
  acquireStateOfArt
  acquireQualificationProtocol
  acquireFailureProbabilityModel
  acquireFaultDetectionSemantics
  acquireCorrectiveActionPolicy
  acquireSubsystemIntegrationReceipt
  : FSPICReverseTarget

record FSPICReverseObligation : Set where
  constructor fsp-ic-reverse-obligation
  field
    target : FSPICReverseTarget
    preferredEvidence : String
    promotes : String
    cannotPromote : String

open FSPICReverseObligation public

------------------------------------------------------------------------
-- CINDI: source provenance is part of the engineering object.
-- NASA explicitly describes a searchable database, numerical filtering/sorting
-- and source information retained for each device.  That is a natural match
-- for DASHI's provenance-carrying technical hypergraph.
------------------------------------------------------------------------

record CINDIDeviceReceipt : Set where
  constructor cindi-device-receipt
  field
    deviceLabel : String
    sensorKind : ICSensorKind
    temperatureCapability : String
    radiationCapability : String
    sourceInformation : String
    sourceRetainedWithDevice : Bool
    sourceRetainedWithDeviceIsTrue : sourceRetainedWithDevice ≡ true

open CINDIDeviceReceipt public

record CINDIBidiBoundary : Set where
  constructor cindi-bidi-boundary
  field
    bestDisplayedPerformanceMeansMissionAdmissible : Bool
    bestDisplayedPerformanceMeansMissionAdmissibleIsFalse :
      bestDisplayedPerformanceMeansMissionAdmissible ≡ false

    missingDatabaseEntryMeansTechnologyDoesNotExist : Bool
    missingDatabaseEntryMeansTechnologyDoesNotExistIsFalse :
      missingDatabaseEntryMeansTechnologyDoesNotExist ≡ false

    sourceRetentionEnablesReverseAudit : Bool
    sourceRetentionEnablesReverseAuditIsTrue :
      sourceRetentionEnablesReverseAudit ≡ true

canonicalCINDIBidiBoundary : CINDIBidiBoundary
canonicalCINDIBidiBoundary =
  cindi-bidi-boundary false refl false refl true refl

------------------------------------------------------------------------
-- Cross-pollination into the existing generic technical-dependency hypergraph.
------------------------------------------------------------------------

leblancNode : Hypergraph.TechnicalNode
leblancNode = Hypergraph.technical-node Hypergraph.personNode "Joshua LeBlanc"

fspICNode : Hypergraph.TechnicalNode
fspICNode = Hypergraph.technical-node Hypergraph.technologyNode "40 kW FSP instrumentation and controls technology maturation"

ficsProgrammeNode : Hypergraph.TechnicalNode
ficsProgrammeNode = Hypergraph.technical-node Hypergraph.programmeNode "NASA Fission Instrumentation & Controls for Space (FICS)"

leblancAuthorshipEdge : Hypergraph.TechnicalHyperedge
leblancAuthorshipEdge =
  Hypergraph.technical-hyperedge
    (leblancNode ∷ fspICNode ∷ [])
    Hypergraph.authoredOrInvented
    Hypergraph.primaryTechnicalReceipt
    "NASA NTRS 20250008475 author list"
    "LeBlanc is a named coauthor of the public I&C Technology Development Path presentation; edge does not claim sole authorship or invention"

ficsProgrammeTechnologyEdge : Hypergraph.TechnicalHyperedge
ficsProgrammeTechnologyEdge =
  Hypergraph.technical-hyperedge
    (ficsProgrammeNode ∷ fspICNode ∷ [])
    Hypergraph.programmeUsesTechnology
    Hypergraph.officialProgrammeReceipt
    "NASA NTRS 20250008475 FICS workshop outcomes and draft I&C technology development path"
    "FICS programme explicitly develops and compares instrumentation/control technologies for FSP/SNP"

------------------------------------------------------------------------
-- Exact attribution boundary.
------------------------------------------------------------------------

leblancFSPAttribution : Attribution.ScientificWorkAttribution
leblancFSPAttribution =
  Attribution.scientific-work-attribution
    "Joshua LeBlanc"
    "NASA 40 kW Fission Surface Power I&C Technology Development Path"
    "NASA Fission Instrumentation & Controls for Space / FSP Technology Maturation"
    Attribution.namedAuthor
    Attribution.primaryInstitutionalRecord
    "NASA NTRS 20250008475"
    "Named coauthor of the presentation; source does not support sole ownership of CINDI, FICS, or the entire 40 kW FSP programme"
    Attribution.externalSourceOwner

leblancTechMatLeadAttribution : Attribution.ScientificWorkAttribution
leblancTechMatLeadAttribution =
  Attribution.scientific-work-attribution
    "Joshua LeBlanc"
    "NASA SNP I&C Technology Maturation"
    "NASA FICS Executive Committee"
    Attribution.namedTechnicalLead
    Attribution.primaryInstitutionalRecord
    "NASA NTRS 20250008475, FICS Executive Committee slide"
    "Source identifies LeBlanc as NASA SNP I&C TechMat Team Lead; this does not imply leadership of every FSP I&C subproject"
    Attribution.externalSourceOwner
