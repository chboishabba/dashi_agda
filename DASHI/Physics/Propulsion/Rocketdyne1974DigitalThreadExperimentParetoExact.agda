{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.Rocketdyne1974DigitalThreadExperimentParetoExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.ITIRInvestigationAcquisitionParetoExact as Pareto
import DASHI.Physics.Propulsion.Rocketdyne1974TerminalPhysicalFrontierExact as Physical
import DASHI.Physics.Propulsion.Rocketdyne1974OperationsReliabilityFrontierExact as OpsRel
import DASHI.Physics.Propulsion.Rocketdyne1974ContemporaryQualificationPHMSourceAtlasExact as SOTA

------------------------------------------------------------------------
-- DIGITAL THREAD
--
-- The same article/revision must remain traceable from requirement and
-- fabrication through inspection, test, anomaly/disposition, serviceability
-- and population reliability.  Shared labels or adjacent programme lineage do
-- not manufacture this same-object thread.
------------------------------------------------------------------------

data ThreadCoordinate : Set where
  requirement articleIdentity materialAndCoating processHistory geometry
  inspection testCondition measuredResponse anomalyDisposition
  approvedRevision serviceability populationReliability : ThreadCoordinate

record DigitalThreadBoundary : Set where
  constructor digital-thread-boundary
  field
    sameObjectTraceRequired : Bool
    sameObjectTraceRequiredIsTrue : sameObjectTraceRequired ≡ true
    testSuccessImpliesQualification : Bool
    testSuccessImpliesQualificationIsFalse : testSuccessImpliesQualification ≡ false
    qualificationImpliesServiceability : Bool
    qualificationImpliesServiceabilityIsFalse : qualificationImpliesServiceability ≡ false
    serviceabilityImpliesFleetReliability : Bool
    serviceabilityImpliesFleetReliabilityIsFalse : serviceabilityImpliesFleetReliability ≡ false
    adjacentProgrammeImpliesTechnologyTransfer : Bool
    adjacentProgrammeImpliesTechnologyTransferIsFalse : adjacentProgrammeImpliesTechnologyTransfer ≡ false
    digitalThreadCreatesHistoricalTruth : Bool
    digitalThreadCreatesHistoricalTruthIsFalse : digitalThreadCreatesHistoricalTruth ≡ false
    boundary : String

digitalThreadBoundary : DigitalThreadBoundary
digitalThreadBoundary = digital-thread-boundary
  true refl
  false refl
  false refl
  false refl
  false refl
  false refl
  "A digital thread is an evidence-preserving same-object join, not a truth generator or a substitute for missing source records."

------------------------------------------------------------------------
-- NON-SCALAR ACQUISITION PORTFOLIO
--
-- Axis values are DASHI routing calibration only.  They rank neither truth nor
-- scientific authority.  The canonical mixed Pareto orientation comes from
-- ITIRInvestigationAcquisitionParetoExact on current master.
------------------------------------------------------------------------

wallGaugeAndContour : Pareto.InvestigationCandidate
wallGaugeAndContour = Pareto.investigation-candidate
  "rocketdyne:wall-gauge-contour"
  "pay local geometry for pressure/thermal stress recovery"
  "engineering drawing / fabrication drawing / dimensional inspection record"
  "public archive first; lawful archival request if not located"
  "R-9557 Test 768 / Test 870-2 exact article revisions"
  "routing calibration: high physics dependency closure"
  10 10 9 8 5
  true refl false refl false refl

test052ThermalField : Pareto.InvestigationCandidate
test052ThermalField = Pareto.investigation-candidate
  "rocketdyne:test052-thermal-field"
  "recover numerical temperature/heat-flux calibration target"
  "thermal-analysis appendix / thermocouple table / original analysis package"
  "public archive first; lawful archival request if not located"
  "R-9557 source-correlated Test 052 model"
  "routing calibration: closes thermal-model reconstruction"
  10 9 8 9 6
  true refl false refl false refl

fabricationTraveler : Pareto.InvestigationCandidate
fabricationTraveler = Pareto.investigation-candidate
  "rocketdyne:fabrication-traveler"
  "recover same-article process/coating/braze/surface-treatment history"
  "traveler, process specification, coating lot, weld/braze and heat-treatment records"
  "public archive / manufacturer archive / lawful records request"
  "Haynes-25 and WC103/VH-101 articles"
  "routing calibration: qualification + constitutive-state closure"
  9 10 10 10 8
  true refl false refl false refl

inspectionNDEHistory : Pareto.InvestigationCandidate
inspectionNDEHistory = Pareto.investigation-candidate
  "rocketdyne:inspection-nde-history"
  "recover pre/post-test defect observability and acceptance state"
  "radiography/dye penetrant/dimensional/NDE inspection and disposition records"
  "public archive / programme records / lawful request"
  "exact article and revision"
  "routing calibration: damage-tolerance and qualification closure"
  9 9 9 10 7
  true refl false refl false refl

constitutiveData : Pareto.InvestigationCandidate
constitutiveData = Pareto.investigation-candidate
  "rocketdyne:period-constitutive-laws"
  "recover temperature-dependent Haynes-25 and WC103/VH-101 strength/creep/oxidation laws"
  "period handbook, material lot data, Rocketdyne/Wah Chang/Haynes qualification data"
  "public technical literature / archives"
  "same material state where identifiable; otherwise bounded comparator"
  "routing calibration: same-model two-material prediction"
  10 10 9 8 6
  true refl false refl false refl

maintenanceFRACAS : Pareto.InvestigationCandidate
maintenanceFRACAS = Pareto.investigation-candidate
  "rocketdyne:maintenance-fracas"
  "recover anomaly, teardown, repair, purge/protection and return-to-service history"
  "maintenance logs, anomaly reports, engineering-change/disposition records"
  "public archive / programme records / lawful request"
  "Moog valve, injector, braze/nozzle exact article histories"
  "routing calibration: serviceability + adaptive qualification closure"
  9 9 10 10 8
  true refl false refl false refl

populationLedger : Pareto.InvestigationCandidate
populationLedger = Pareto.investigation-candidate
  "rocketdyne:reliability-population-ledger"
  "define homogeneous article population and denominator for reliability inference"
  "serial/lot/revision ledger with inspected, failed, repaired, removed and returned-to-service counts"
  "programme/manufacturer records"
  "Rocketdyne/Moog population only; Bell/Marquardt kept separate"
  "routing calibration: population reliability denominator"
  8 8 9 10 9
  true refl false refl false refl

sourceSelectionRecords : Pareto.InvestigationCandidate
sourceSelectionRecords = Pareto.investigation-candidate
  "rocketdyne:source-selection-lineage"
  "resolve whether/how INTEREGEN influenced selected Marquardt Shuttle RCS"
  "NASA source-selection, procurement, design-review and requirement-trace records"
  "lawful historical acquisition only"
  "Rocketdyne demonstrator -> NASA decision object -> Marquardt selected system"
  "routing calibration: historical lineage only; does not pay thermo-mechanics"
  8 5 5 10 9
  true refl false refl false refl

record AcquisitionPortfolio : Set where
  constructor acquisition-portfolio
  field
    candidates : List Pareto.InvestigationCandidate
    scalarTruthScoreUsed : Bool
    candidatePriorityCreatesEvidence : Bool
    canonicalParetoBoundary : Pareto.InvestigationAcquisitionBoundary
    rationale : String

rocketdyneAcquisitionPortfolio : AcquisitionPortfolio
rocketdyneAcquisitionPortfolio = acquisition-portfolio
  (wallGaugeAndContour ∷
   test052ThermalField ∷
   fabricationTraveler ∷
   inspectionNDEHistory ∷
   constitutiveData ∷
   maintenanceFRACAS ∷
   populationLedger ∷
   sourceSelectionRecords ∷ [])
  false false
  Pareto.canonicalInvestigationAcquisitionBoundary
  "Prefer acquisitions that close multiple same-object physics/qualification/serviceability residuals; never scalarize priority into truth or authority."

record RocketdyneDigitalThreadExperimentFrontier : Set where
  constructor rocketdyne-digital-thread-experiment-frontier
  field
    physicalFrontier : Physical.TerminalFrontier
    operationsReliabilityFrontier : OpsRel.RocketdyneOperationsReliabilityFrontier
    sourceAtlasBoundary : SOTA.ContemporarySourceAtlasBoundary
    threadBoundary : DigitalThreadBoundary
    acquisitionPortfolio : AcquisitionPortfolio
    firstPhysicsProducer : String
    firstQualificationProducer : String
    firstReliabilityProducer : String
    stoppingRule : String

rocketdyneDigitalThreadExperimentFrontier : RocketdyneDigitalThreadExperimentFrontier
rocketdyneDigitalThreadExperimentFrontier = rocketdyne-digital-thread-experiment-frontier
  Physical.currentTerminalFrontier
  OpsRel.rocketdyneOperationsReliabilityFrontier
  SOTA.contemporarySourceAtlasBoundary
  digitalThreadBoundary
  rocketdyneAcquisitionPortfolio
  "Recover local wall gauge/contour plus Test-052 numerical thermal field, then instantiate one same-model Haynes/WC103 thermo-structural discriminator."
  "Recover fabrication/process + inspection/NDE + formal disposition/approval on the exact article revision."
  "Recover a homogeneous serial/lot/revision population with complete exposure/failure/repair/removal/return-to-service counts."
  "If the required same-object producers cannot be recovered, retain empirical discrimination and non-identifiability rather than manufacturing unique stress, lifetime, qualification or fleet reliability."
