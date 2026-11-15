{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.Rocketdyne1974InspectionCapabilityPODExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- INSPECTION CAPABILITY / POD FRONTIER
--
-- NASA-STD-5009C requires quantitative probability-of-detection support when
-- fracture-control claims rely on NDE.  That is a contemporary engineering
-- comparator only: it does not retroactively impose a 2023 standard on the
-- 1974 Rocketdyne programme, and it does not create missing inspection data.
------------------------------------------------------------------------

record InspectionCapability : Set where
  constructor inspection-capability
  field
    methodReference : String
    defectClassReference : String
    coverageReference : String
    sensitivityOrPODReference : String
    acceptanceThresholdReference : String
    articleRevisionReference : String
    inspectionTimeReference : String
    exactHistoricalReceiptRecovered : Bool

historicalRocketdyneInspectionCapability : InspectionCapability
historicalRocketdyneInspectionCapability = inspection-capability
  "specific pre/post-test NDE method not recovered for the exact nozzle article"
  "defect class / flaw morphology not quantitatively bound"
  "coverage not recovered"
  "quantitative sensitivity / POD not recovered"
  "acceptance threshold not recovered"
  "exact article/revision inspection binding not recovered"
  "inspection chronology relative to firing not recovered"
  false

record InspectionCapabilityFrontier : Set where
  constructor inspection-capability-frontier
  field
    inspectionPresenceEnoughForFractureCriticalClaim : Bool
    quantitativePODNeededWhenDetectionCreditIsClaimed : Bool
    exactMethodPaid : Bool
    exactCoveragePaid : Bool
    exactDefectClassPaid : Bool
    exactSensitivityOrPODPaid : Bool
    exactAcceptanceThresholdPaid : Bool
    exactArticleRevisionBindingPaid : Bool
    exactInspectionChronologyPaid : Bool
    modernRequirementAppliesRetroactively : Bool
    sourceReference : String
    boundary : String

canonicalInspectionCapabilityFrontier : InspectionCapabilityFrontier
canonicalInspectionCapabilityFrontier = inspection-capability-frontier
  false true
  false false false false false false false
  false
  "NASA-STD-5009C (2023), Nondestructive Evaluation Requirements for Fracture Critical Metallic Components; NASA-STD-5019A Change 4 (2024)"
  "Recover the historical inspection method, coverage, defect class, sensitivity/POD basis, acceptance threshold, article/revision binding and chronology before using inspection as a quantitative damage-tolerance payment."

quantitativePODRequiredForFractureCriticalClaim : Bool
quantitativePODRequiredForFractureCriticalClaim = true

inspectionPresenceDoesNotPayDetectionCapability : Bool
inspectionPresenceDoesNotPayDetectionCapability = true

historicalInspectionCapabilityUnpaid : Bool
historicalInspectionCapabilityUnpaid = true

modernPODRequirementDoesNotApplyRetroactively : Bool
modernPODRequirementDoesNotApplyRetroactively = true
