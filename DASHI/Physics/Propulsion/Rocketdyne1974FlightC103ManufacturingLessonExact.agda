{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.Rocketdyne1974FlightC103ManufacturingLessonExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- LATER FLIGHT C-103 MANUFACTURING LESSON
--
-- Primary related-work anchors:
--   * NASA/TP-2005-214053, NESC Independent Assessment of Space Shuttle
--     Reaction Control System C-103 Thruster Cracking
--   * JSC Materials Laboratory reproduction/failure-analysis work
--
-- These are later Shuttle flight-hardware findings. They do NOT identify the
-- root cause of the 1974 Rocketdyne WC103 + VH-101 test article. Their value
-- here is methodological: material identity and service temperature are not
-- sufficient state variables; manufacturing/process history and inspection
-- observability can be decisive survivability coordinates.
------------------------------------------------------------------------

data EvidenceRelation : Set where
  sameObjectEvidence relatedWorkMethodology : EvidenceRelation

record FlightC103CrackingLesson : Set where
  constructor flight-c103-cracking-lesson
  field
    hardwareClass : String
    material : String
    historicalCrackPopulation : String
    laterTriggerEvent : String
    reportedRootCause : String
    reproducedNecessaryConditions : String
    inspectionChallenge : String
    documentationChallenge : String
    relationshipToRocketdyne1974 : EvidenceRelation
    sameHistoricalArticle : Bool
    sourceReference : String

shuttleC103CrackingLesson : FlightC103CrackingLesson
shuttleC103CrackingLesson =
  flight-c103-cracking-lesson
    "Space Shuttle RCS C-103 primary-thruster injector/chamber hardware"
    "C-103 niobium alloy"
    "relief-radius cracking had previously been observed in seven thrusters prior to flight"
    "April 2004 discovery of counter-bore and relief-radius cracks in primary thruster S/N 120 prompted NESC independent assessment"
    "intergranular cracking due to hydrogen embrittlement produced during manufacturing while processing thrusters with fluoride-containing acids"
    "mechanically disturbed/cold-worked free surface + sustained tensile stress near yield + fluorine-containing fluid + sustained temperature above 400 F"
    "previous analyses lacked reliable inspection controls sufficient to prevent cracked thrusters from entering the fleet"
    "previous failure analyses lacked sufficient documentation to substantiate the earlier stress-corrosion/hot-salt root-cause conclusions"
    relatedWorkMethodology
    false
    "NASA/TP-2005-214053 / NTRS 20060000024; JSC reproduction abstract NTRS 20060052517"

manufacturingProcessIsIndependentCoordinate : Bool
manufacturingProcessIsIndependentCoordinate = true

historicalCauseDoesNotTransferToRocketdyne : Bool
historicalCauseDoesNotTransferToRocketdyne = true

record ManufacturingCoordinateBoundary : Set where
  constructor manufacturing-coordinate-boundary
  field
    alloyIdentityAloneSufficient : Bool
    peakTemperatureAloneSufficient : Bool
    manufacturingRouteRequiredForFullSurvivabilityState : Bool
    surfaceConditionRequiredForFullSurvivabilityState : Bool
    chemicalProcessExposureRequiredForFullSurvivabilityState : Bool
    residualOrAppliedStressRequiredForFullSurvivabilityState : Bool
    inspectionObservabilityRequiredForQualificationClaim : Bool
    laterFlightRootCauseMayBeAssignedTo1974ArticleWithoutSameObjectEvidence : Bool

canonicalManufacturingCoordinateBoundary : ManufacturingCoordinateBoundary
canonicalManufacturingCoordinateBoundary =
  manufacturing-coordinate-boundary
    false false true true true true true false

record DocumentationLesson : Set where
  constructor documentation-lesson
  field
    priorFailureAnalysisExisted : Bool
    priorAnalysisWasSufficientlyDocumentedForClosure : Bool
    laterIndependentReconstructionNeeded : Bool
    rootCauseClaimRequiresTraceableProcessAndInspectionEvidence : Bool
    admissibleUse : String

nescDocumentationLesson : DocumentationLesson
nescDocumentationLesson =
  documentation-lesson
    true false true true
    "Use the later NESC history as a provenance/qualification lesson: an asserted historical root cause is not closed merely because an earlier failure analysis existed."

record Rocketdyne1974ProcessAcquisitionFrontier : Set where
  constructor process-acquisition-frontier
  field
    exactWC103ManufacturingRouteRecovered : Bool
    exactVH101CoatingProcessRecovered : Bool
    surfaceTreatmentRecovered : Bool
    residualStressStateRecovered : Bool
    inspectionAcceptanceHistoryRecovered : Bool
    articleSpecificFailureAnalysisRecovered : Bool
    nextSource : String

rocketdyne1974ProcessAcquisitionFrontier : Rocketdyne1974ProcessAcquisitionFrontier
rocketdyne1974ProcessAcquisitionFrontier =
  process-acquisition-frontier
    false false false false false false
    "Acquire the 1974 WC103/VH-101 nozzle fabrication traveler/process specification, coating/braze records, inspection disposition and article-specific post-test examination before importing any later Shuttle C-103 cracking mechanism."
