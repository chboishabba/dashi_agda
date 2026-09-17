module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseOpenMMCVOracleExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseAtomisticConfigurationExact as Config
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSourceAtomSelectionExact as Selection
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseAtomisticCVProjectionExact as Projection

------------------------------------------------------------------------
-- OPENMM EXECUTABLE ORACLE CONTRACT
--
-- OpenMM is an independent executable comparison surface, not formal authority.
-- OpenMM 8.6 documentation states that CustomCentroidBondForce computes group
-- centers as user-weighted averages of particle positions and supports geometry
-- over those centers; CustomCVForce exposes scalar position-dependent CVs.
-- This owner records that capability and the shape of a future same-object
-- comparison receipt.  No comparison is marked executed in this session.
------------------------------------------------------------------------

openMMDocumentationIdentity : Identity.ExternalIdentityDemand
openMMDocumentationIdentity =
  Identity.mkOptionalIdentityDemand
    "AdK external CV evaluator"
    "OpenMM 8.6 custom-force documentation"
    "OpenMM CustomCentroidBondForce and CustomCVForce"
    Identity.canonicalURL
    (Identity.verified
      "OpenMM User Guide 8.6 inspected 2026-09-17"
      "https://docs.openmm.org/latest/userguide/theory/03_custom_forces.html")

openMMQID : Identity.ExternalIdentityDemand
openMMQID =
  Identity.mkOptionalIdentityDemand
    "AdK external CV evaluator"
    "OpenMM software QID"
    "OpenMM"
    Identity.wikidataQid
    (Identity.unresolved "software QID not independently verified in this tranche")

openMMDeweyCoordinate : String
openMMDeweyCoordinate =
  "software/documentation Dewey coordinate unresolved; canonical documentation URL retained"

record OpenMMCapabilityReceipt : Set where
  constructor openmm-capability-receipt
  field
    documentationIdentity : Identity.ExternalIdentityDemand
    qid : Identity.ExternalIdentityDemand
    deweyCoordinate : String
    centroidGroupsUseUserWeights : Bool
    centroidGeometrySupportsDistances : Bool
    centroidGeometrySupportsAngles : Bool
    customCVSupportsScalarPositionFunctions : Bool
    capabilityCreatesAdKSourceAuthority : Bool
open OpenMMCapabilityReceipt public

canonicalOpenMMCapabilityReceipt : OpenMMCapabilityReceipt
canonicalOpenMMCapabilityReceipt = openmm-capability-receipt
  openMMDocumentationIdentity
  openMMQID
  openMMDeweyCoordinate
  true true true true false

------------------------------------------------------------------------
-- Same-object comparison contract.
------------------------------------------------------------------------

record NumericalTolerance : Set where
  constructor numerical-tolerance
  field
    thetaOneToleranceReading : String
    thetaTwoToleranceReading : String
    dLnToleranceReading : String
    comparisonArithmetic : String
open NumericalTolerance public

record OpenMMCVResult : Set where
  constructor openmm-cv-result
  field
    thetaOneReading : String
    thetaTwoReading : String
    dLnReading : String
    unitConvention : String
    selectedParticleManifestHash : String
    coordinateManifestHash : String
    evaluatorVersion : String
open OpenMMCVResult public

record OpenMMComparisonReceipt
  (configuration : Config.AtomisticConfiguration) : Set₁ where
  constructor openmm-comparison-receipt
  field
    sourceConfiguration : Config.AtomisticConfiguration
    sameConfiguration : sourceConfiguration ≡ configuration
    selectionBundle : Selection.AdKThreeCVSelections
    openMMResult : OpenMMCVResult
    dashiObservationReference : String
    tolerance : NumericalTolerance
    sameSelectedAtomsChecked : Bool
    sameMassWeightsChecked : Bool
    sameCoordinateBytesChecked : Bool
    agreementWithinTolerance : Bool
    executionLogReference : String
    executionActuallyObserved : Bool
    externalAgreementCreatesFormalAuthority : Bool
open OpenMMComparisonReceipt public

unexecutedComparisonTemplate :
  (configuration : Config.AtomisticConfiguration) →
  OpenMMComparisonReceipt configuration
unexecutedComparisonTemplate configuration = openmm-comparison-receipt
  configuration
  refl
  Selection.canonicalAdKThreeCVSelections
  (openmm-cv-result
    "unexecuted"
    "unexecuted"
    "unexecuted"
    "degrees for theta1/theta2; angstrom for dLN after explicit unit conversion"
    "unpaid"
    "unpaid"
    "OpenMM 8.6 documentation capability only; executable version not observed")
  "DASHI observation must be generated from the same AtomisticConfiguration"
  (numerical-tolerance
    "must be declared before execution"
    "must be declared before execution"
    "must be declared before execution"
    "comparison arithmetic/tolerance policy must be predeclared")
  false false false false
  "no execution log in this connector-only tranche"
  false false

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data OpenMMAgreementCreatesFormalAuthority : Set where
data DocumentationCreatesExecutedComparison : Set where
data SamePDBLabelCreatesSameCoordinateBytes : Set where
data SameParticleIndicesCreateSameMassWeights : Set where

openMMAgreementDoesNotCreateFormalAuthority : OpenMMAgreementCreatesFormalAuthority → ⊥
openMMAgreementDoesNotCreateFormalAuthority ()

documentationDoesNotCreateExecutedComparison : DocumentationCreatesExecutedComparison → ⊥
documentationDoesNotCreateExecutedComparison ()

samePdbLabelDoesNotCreateSameBytes : SamePDBLabelCreatesSameCoordinateBytes → ⊥
samePdbLabelDoesNotCreateSameBytes ()

sameIndicesDoNotCreateSameMassWeights : SameParticleIndicesCreateSameMassWeights → ⊥
sameIndicesDoNotCreateSameMassWeights ()

record AdKOpenMMCVOracleBoundary : Set where
  constructor adk-openmm-cv-oracle-boundary
  field
    openMMCentroidCapabilityRetained : Bool
    customCVCapabilityRetained : Bool
    canonicalDocumentationIdentityRetained : Bool
    openMMQidExplicitlyUnresolved : Bool
    openMMDeweyExplicitlyUnresolved : Bool
    sameConfigurationComparisonRequired : Bool
    sameSelectionManifestRequired : Bool
    sameMassWeightsRequired : Bool
    sameCoordinateBytesRequired : Bool
    toleranceMustBeDeclared : Bool
    openMMAgreementCreatesFormalAuthority : Bool
    documentationCreatesExecutedComparison : Bool
    comparisonExecutionPaidHere : Bool
open AdKOpenMMCVOracleBoundary public

canonicalAdKOpenMMCVOracleBoundary : AdKOpenMMCVOracleBoundary
canonicalAdKOpenMMCVOracleBoundary =
  adk-openmm-cv-oracle-boundary
    true true true true true true true true true true
    false false false
