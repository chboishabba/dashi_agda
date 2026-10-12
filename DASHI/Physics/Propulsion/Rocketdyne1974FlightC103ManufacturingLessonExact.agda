{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.Rocketdyne1974FlightC103ManufacturingLessonExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- LATER FLIGHT C-103 MANUFACTURING LESSON
--
-- Primary related-work anchors:
--   * NASA/TP-2005-214053, NESC Independent Assessment of Space Shuttle
--     Reaction Control System C-103 Thruster Cracking
--   * NASA/NESC follow-on reproduction / root-cause work
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
    "seven relief-radius cracks reported in 1979-1982 production/inspection history"
    "2004 discovery of an additional crack on thruster S/N 120 prompted NESC independent assessment"
    "hydrogen embrittlement introduced during manufacturing, associated with fluoride/HF-containing pre-weld etchant exposure"
    "cold-worked/mechanically disturbed free surface + sustained tensile stress near yield + fluorine-containing fluid + sustained temperature above about 400 F"
    "reliable in-situ nondestructive detection/inspection controls were inadequate for the crack population at the relevant stage"
    "earlier 1970s/1980s failure analyses and root-cause documentation were judged insufficiently documented for confident closure"
    relatedWorkMethodology
    false
    "NASA/TP-2005-214053; NESC C-103 thruster-cracking reproduction/root-cause reports"

------------------------------------------------------------------------
-- METHOD TRANSFER, NOT CAUSE TRANSFER
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- DOCUMENTATION / ROOT-CAUSE LESSON
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- IMPACT ON THE 1974 MAX-CUT
------------------------------------------------------------------------

record Rocketdyne1974ProcessAcquisitionFrontier : Set where
  constructor process-acquisition-frontier
  field
    exactWC103ManufacturingRouteRecovered : Bool
    exactVH101CoatingProcessRecovered : Bool
    prebrazeOrPreweldSurfaceTreatmentRecovered : Bool
    residualStressStateRecovered : Bool
    inspectionAcceptanceHistoryRecovered : Bool
    articleSpecificFailureAnalysisRecovered : Bool
    nextSource : String

rocketdyne1974ProcessAcquisitionFrontier : Rocketdyne1974ProcessAcquisitionFrontier
rocketdyne1974ProcessAcquisitionFrontier =
  process-acquisition-frontier
    false false false false false false
    "Acquire the 1974 WC103/VH-101 nozzle fabrication traveler/process specification, coating/braze records, inspection disposition and article-specific post-test examination before importing any later Shuttle C-103 cracking mechanism."
