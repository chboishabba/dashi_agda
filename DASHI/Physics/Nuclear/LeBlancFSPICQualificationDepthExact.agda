module DASHI.Physics.Nuclear.LeBlancFSPICQualificationDepthExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

-- NASA 40 kW FSP I&C Technology Development Path, NTRS 20250008475.
-- Source distinguishes reference-system requirements, SOA comparison,
-- reliability physics / accelerated testing, autonomy and corrective action.

data QualificationAxis : Set where
  neutronFluence gammaDose temperature operatingLife measurementIntegrity compactness autonomy failureProbability : QualificationAxis

data QualificationEvidence : Set where
  heritageKnowledge
  literatureDeviceRecord
  acceleratedTest
  reliabilityPhysicsModel
  integratedSystemTest
  : QualificationEvidence

record QualificationRequirement : Set where
  constructor qualification-requirement
  field
    axis : QualificationAxis
    sourceReading : String
    verificationPath : String
    sourceReference : String

open QualificationRequirement public

failureProbabilityRequirement : QualificationRequirement
failureProbabilityRequirement = qualification-requirement
  failureProbability
  "quantify probability of failure and determine what standards to adopt or introduce"
  "high-accelerated testing, reliability-physics models, or both"
  "NASA NTRS 20250008475, Drivers of I&C Maturity and Gap Analysis"

measurementIntegrityRequirement : QualificationRequirement
measurementIntegrityRequirement = qualification-requirement
  measurementIntegrity
  "measurement integrity requires operating margins compatible with FSP performance specifications"
  "calibrated sensor performance under the relevant environment and life conditions"
  "NASA NTRS 20250008475"

record SensorQualificationChain : Set where
  constructor sensor-qualification-chain
  field
    referenceSystem : String
    requirementEnvelope : String
    candidateTechnology : String
    stateOfArtEvidence : String
    gapAssessment : String
    qualificationProtocol : String
    systemIntegration : String
    autonomyPolicy : String

open SensorQualificationChain public

canonicalQualificationChain : SensorQualificationChain
canonicalQualificationChain = sensor-qualification-chain
  "define the FSP/SNP reference system and notional sensor location"
  "temperature, neutron/gamma environment, life, size, measurement integrity and reliability"
  "candidate sensor/device from heritage, literature or CINDI"
  "compare documented SOA performance to each requirement coordinate"
  "formulate gap, technical barrier and risk where requirement is not closed"
  "accelerated test and/or reliability-physics model with mission-relevant calibration"
  "integrate sensor, diagnostics, communications and control software"
  "self-diagnosis/fault detection may trigger automated off-normal response only through an explicit corrective-action policy"

record LeBlancQualificationBoundary : Set where
  constructor leblanc-qualification-boundary
  field
    CINDIBestPerformanceEqualsQualified : Bool
    CINDIBestPerformanceEqualsQualifiedIsFalse : CINDIBestPerformanceEqualsQualified ≡ false
    heritageUseEliminatesSpaceQualification : Bool
    heritageUseEliminatesSpaceQualificationIsFalse : heritageUseEliminatesSpaceQualification ≡ false
    acceleratedTestAloneProvesTenYearReliability : Bool
    acceleratedTestAloneProvesTenYearReliabilityIsFalse : acceleratedTestAloneProvesTenYearReliability ≡ false
    faultDetectionAloneDefinesCorrectiveAction : Bool
    faultDetectionAloneDefinesCorrectiveActionIsFalse : faultDetectionAloneDefinesCorrectiveAction ≡ false
    probabilityOfFailureNeedsModelOrTestReceipt : Bool
    probabilityOfFailureNeedsModelOrTestReceiptIsTrue : probabilityOfFailureNeedsModelOrTestReceipt ≡ true

canonicalLeBlancQualificationBoundary : LeBlancQualificationBoundary
canonicalLeBlancQualificationBoundary = leblanc-qualification-boundary false refl false refl false refl false refl true refl

data LeBlancQualificationReverseTarget : Set where
  acquireOperatingMargin
  acquireRadiationDriftCurve
  acquireTemperatureDriftCurve
  acquireLifeAccelerationModel
  acquireFailureProbabilityModel
  acquireRedundancyArchitecture
  acquireDiagnosticCoverage
  acquireCorrectiveActionPolicy
  : LeBlancQualificationReverseTarget
