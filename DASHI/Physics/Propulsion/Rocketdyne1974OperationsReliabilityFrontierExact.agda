{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.Rocketdyne1974OperationsReliabilityFrontierExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Propulsion.CorkySoftManufacturingMissionOperationsBidiExact as Ops
import DASHI.Physics.Propulsion.ReliabilityCapacityResourceDemandBidiExact as Rel
import DASHI.Physics.Propulsion.Rocketdyne1974HotSectionQualificationFrontierExact as Hot
import DASHI.Physics.Propulsion.Rocketdyne1974OperationalValveReliabilityLessonExact as Valve

------------------------------------------------------------------------
-- OPERATIONS / RELIABILITY REVERSE-PAYMENT WELD
--
-- The 1974 archive pays article-level environmental/hot-fire observations and
-- several concrete maintenance problems.  It does not pay the stronger objects
-- needed for an operational/fleet statement: installed-configuration identity,
-- same-object serviceability history, maintenance disposition, lot/population
-- identity, removal counts, or qualified/serviceable population counts.
--
-- This owner maps those residuals into existing generic propulsion operations
-- and reliability-capacity reverse targets.  It intentionally constructs no
-- fleet reliability rate and no operational Shuttle identity for R-9557.
------------------------------------------------------------------------

installedConfigurationObligation : Ops.OperationsReverseObligation
installedConfigurationObligation =
  Ops.operations-reverse-obligation
    Ops.acquireInstalledConfiguration
    "article-level configuration ledger tying the exact valve/injector/nozzle revisions to each test and any later installed system"
    "same-object installed/configured article history"
    "cannot infer installed flight configuration from a technology-demonstrator test article"

serviceabilityStateObligation : Ops.OperationsReverseObligation
serviceabilityStateObligation =
  Ops.operations-reverse-obligation
    Ops.acquireServiceabilityState
    "inspection/maintenance release state after each environmental and hot-fire exposure, including valve leakage and injector-plugging disposition"
    "bounded same-object serviceability state"
    "continued firing or absence of a reported incident does not prove serviceability"

maintenanceFindingsObligation : Ops.OperationsReverseObligation
maintenanceFindingsObligation =
  Ops.operations-reverse-obligation
    Ops.acquireMaintenanceFindings
    "maintenance teardown, contamination, seal-abrasion, injector-plugging, braze/nozzle findings and disposition records for the exact articles"
    "append-only maintenance finding history"
    "cannot turn a summary narrative into a complete maintenance/FRACAS record"

lotSupplierRevisionObligation : Ops.OperationsReverseObligation
lotSupplierRevisionObligation =
  Ops.operations-reverse-obligation
    Ops.acquireLotSupplierRevisionHistory
    "Moog valve serial/lot and revision history; injector/nozzle/coating supplier and article revision lineage"
    "supplier/lot/revision coordinate for repeated-failure interpretation"
    "two similar serial failures do not define a homogeneous production population without lot/revision identity"

approvedRevisionObligation : Ops.OperationsReverseObligation
approvedRevisionObligation =
  Ops.operations-reverse-obligation
    Ops.acquireApprovedQualificationRevision
    "engineering-change order, anomaly disposition, review and approval records for valve protection/purge, nozzle material changes and qualification-envelope revisions"
    "approved bounded qualification/operations revision"
    "source-reported recommendation or successful follow-up does not prove formal approval"

record OperationsObligationBundle : Set where
  constructor operations-obligation-bundle
  field
    installedConfiguration : Ops.OperationsReverseObligation
    serviceabilityState : Ops.OperationsReverseObligation
    maintenanceFindings : Ops.OperationsReverseObligation
    lotSupplierRevision : Ops.OperationsReverseObligation
    approvedRevision : Ops.OperationsReverseObligation

operationsObligations : OperationsObligationBundle
operationsObligations =
  operations-obligation-bundle
    installedConfigurationObligation
    serviceabilityStateObligation
    maintenanceFindingsObligation
    lotSupplierRevisionObligation
    approvedRevisionObligation

populationIdentityObligation : Rel.ReliabilityCapacityReverseObligation
populationIdentityObligation =
  Rel.reliability-capacity-reverse-obligation
    Rel.acquirePopulationIdentity
    "defined Rocketdyne/Moog article population with common revision, environment and observation window"
    "same-population denominator for reliability inference"
    "cannot pool Bell, Rocketdyne and later Shuttle/Marquardt hardware into one reliability population"

rejectRemovalCountObligation : Rel.ReliabilityCapacityReverseObligation
rejectRemovalCountObligation =
  Rel.reliability-capacity-reverse-obligation
    Rel.acquireDefectRejectRemovalCounts
    "complete counts of inspected articles, valve/injector/nozzle rejects, removals, repairs and returns to service"
    "bounded defect/removal frequency on one defined population"
    "two observed valve failures do not by themselves produce a fleet failure rate"

qualifiedServiceabilityObligation : Rel.ReliabilityCapacityReverseObligation
qualifiedServiceabilityObligation =
  Rel.reliability-capacity-reverse-obligation
    Rel.acquireQualifiedYieldOrServiceability
    "same-window counts of qualified and serviceable articles after environmental/hot-fire testing and any approved revisions"
    "qualified/serviceable population coordinate"
    "design goals and mission-equivalent tests do not establish qualified available capacity"

availabilityCustodyObligation : Rel.ReliabilityCapacityReverseObligation
availabilityCustodyObligation =
  Rel.reliability-capacity-reverse-obligation
    Rel.acquirePhysicalAvailabilityAndCustody
    "physical custody, quarantine, installation/removal and return-to-service history for each exact article"
    "physical availability/custody coordinate"
    "qualification or successful test does not prove operational availability"

record ReliabilityObligationBundle : Set where
  constructor reliability-obligation-bundle
  field
    populationIdentity : Rel.ReliabilityCapacityReverseObligation
    rejectRemovalCounts : Rel.ReliabilityCapacityReverseObligation
    qualifiedServiceability : Rel.ReliabilityCapacityReverseObligation
    availabilityCustody : Rel.ReliabilityCapacityReverseObligation

reliabilityObligations : ReliabilityObligationBundle
reliabilityObligations =
  reliability-obligation-bundle
    populationIdentityObligation
    rejectRemovalCountObligation
    qualifiedServiceabilityObligation
    availabilityCustodyObligation

record ServiceabilityPopulationBoundary : Set where
  constructor serviceability-population-boundary
  field
    articleLevelFailureMechanismEvidenceExists : Bool
    articleLevelQualificationEvidenceExists : Bool
    formalServiceabilityReleaseHistoryRecovered : Bool
    homogeneousReliabilityPopulationRecovered : Bool
    completeRemovalRepairCountsRecovered : Bool
    designMissionCountIsObservedPopulationCount : Bool
    laterShuttleValveRateTransfersTo1974Rocketdyne : Bool
    oneSuccessfulFollowupEstablishesFleetReliability : Bool
    boundary : String

serviceabilityPopulationBoundary : ServiceabilityPopulationBoundary
serviceabilityPopulationBoundary =
  serviceability-population-boundary
    true true false false false false false false
    "R-9557 supports article-level mechanisms/tests; operational serviceability and population reliability require same-object maintenance, revision, population and count receipts."

record RocketdyneOperationsReliabilityFrontier : Set where
  constructor rocketdyne-operations-reliability-frontier
  field
    qualificationFrontier : Hot.RocketdyneQualificationReverseFrontier
    operationsFrontier : OperationsObligationBundle
    reliabilityFrontier : ReliabilityObligationBundle
    populationBoundary : ServiceabilityPopulationBoundary
    genericOperationsBoundary : Ops.CorkySoftManufacturingMissionOperationsBoundary
    genericReliabilityBoundary : Rel.ReliabilityCapacityResourceBoundary
    laterOperationalValveComparator : Valve.OperationalValveReliabilityBoundary
    currentExternalProducer : String

rocketdyneOperationsReliabilityFrontier : RocketdyneOperationsReliabilityFrontier
rocketdyneOperationsReliabilityFrontier =
  rocketdyne-operations-reliability-frontier
    Hot.rocketdyneQualificationReverseFrontier
    operationsObligations
    reliabilityObligations
    serviceabilityPopulationBoundary
    Ops.canonicalCorkySoftManufacturingMissionOperationsBoundary
    Rel.canonicalReliabilityCapacityResourceBoundary
    Valve.operationalValveReliabilityBoundary
    "Recover exact maintenance/teardown/anomaly-disposition records, valve/injector/nozzle revision and lot lineage, installed-configuration/serviceability history, and a defined article population with complete reject/removal/repair/return-to-service counts."
