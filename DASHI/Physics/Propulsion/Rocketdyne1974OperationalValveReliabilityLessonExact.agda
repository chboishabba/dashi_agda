{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.Rocketdyne1974OperationalValveReliabilityLessonExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- LATER OPERATIONAL SHUTTLE VALVE RELIABILITY LESSON
--
-- NASA NTRS 19950009917 reports fail-leak/fail-off primary RCS thrusters at
-- roughly 1.5 per flight, attributed primarily to metal nitrate formation in
-- N2O4 pilot-operated valves.  WSTF developed DI-water + GN2 flushing and
-- acceptance retest; 68% recovery was reported from Mar 1992 to Sep 1993.
--
-- This is a shared valve-reliability/contamination coordinate with the 1974
-- Rocketdyne programme, but the mechanisms are different: later metal nitrate
-- chemistry is not the earlier sand/dust migration and Teflon abrasion.
------------------------------------------------------------------------

record OperationalValveLesson : Set where
  constructor operational-valve-lesson
  field
    system : String
    observedFailureModes : String
    reportedRateTenthsPerFlight : Nat
    reportedPrimaryMechanism : String
    recoveryProcess : String
    recoveryPercent : Nat
    recoveryWindow : String
    sourceReference : String

shuttleMetalNitrateValveLesson : OperationalValveLesson
shuttleMetalNitrateValveLesson = operational-valve-lesson
  "Space Shuttle primary RCS"
  "fail-leak / fail-off thruster events"
  15
  "metal nitrate formation in nitrogen-tetroxide pilot-operated valves"
  "deionized-water flushing + gaseous-nitrogen processing followed by comprehensive acceptance test"
  68
  "March 1992 through September 1993"
  "NASA NTRS 19950009917"

sharedValveReliabilityCoordinate : Bool
sharedValveReliabilityCoordinate = true

differentFailureMechanismFromRocketdyneSand : Bool
differentFailureMechanismFromRocketdyneSand = true

record OperationalValveReliabilityBoundary : Set where
  constructor operational-valve-reliability-boundary
  field
    valveReliabilityRemainedOperationallyImportant : Bool
    laterContaminationMechanismEquals1974SandMechanism : Bool
    laterOperationalRateMayBeAssignedTo1974ValvePopulation : Bool
    maintenanceRecoveryCanBeAQualificationFeedbackCoordinate : Bool
    laterExperienceGuidesAcquisition : Bool
    boundary : String

operationalValveReliabilityBoundary : OperationalValveReliabilityBoundary
operationalValveReliabilityBoundary = operational-valve-reliability-boundary
  true false false true true
  "Later Shuttle experience confirms valve contamination/serviceability remained an operational reliability coordinate, but neither its metal-nitrate mechanism nor its per-flight rate transfers to the 1974 Moog 54X107A sand/dust population."
