{-# OPTIONS --safe #-}
module DASHI.Physics.ExoticGravity.AntigravitySourceNativeShortestPathMaxCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.Foundations.CMP119AntigravitySourceVacuumIsraelAdmissionExact as Admission
import DASHI.Physics.Foundations.CMP119AntigravityEq223MetricStressReuseMaxCutExact as Reuse
import DASHI.Physics.ExoticGravity.AntigravitySourceNativeReuseTerminalExact as Terminal

------------------------------------------------------------------------
-- SOURCE-NATIVE ANTIGRAVITY SHORTEST-PATH RECUT
--
-- The previous terminal correctly exposed BOTH of the remaining source/physics
-- seams, but scheduled them conjunctively.  They belong to two different
-- closure routes:
--
--   V / VACUUM-ISRAEL ROUTE
--     actual source vacuum values
--       -> SourceVacuumIsraelAdmission
--       -> already-owned thin-wall Israel/Kottler geometry.
--
--   R / CONTINUUM-STRESS ROUTE
--     literal Eq.(2.23) metric response
--       -> direct finite/R136 same-object response weld
--       -> continuum stress / acceleration consumer.
--
-- Therefore a shortest-path proof must not charge the R136 response weld to V,
-- nor the two-scale Israel admission to R.  Finite-thickness wall dynamics and
-- source-native potential dynamics are optional strengthenings beyond the exact
-- thin-wall V consumer, not premises of that consumer.
------------------------------------------------------------------------

record VacuumIsraelRouteBoundary : Set where
  constructor vacuum-israel-route-boundary
  field
    sourceVacuumReadoutAlreadyOwned : Bool
    cosmologicalStressShapeAlreadyOwned : Bool
    thinWallIsraelGeometryAlreadyOwned : Bool
    sourceVacuumIsraelAdmissionRequired : Bool
    r136FiniteContinuumResponseWeldRequired : Bool
    finiteThicknessWallRequired : Bool
    sourceNativePotentialDynamicsRequired : Bool
    physicalCalibrationRequired : Bool

canonicalVacuumIsraelRouteBoundary : VacuumIsraelRouteBoundary
canonicalVacuumIsraelRouteBoundary =
  vacuum-israel-route-boundary
    true true true true false false false true

record ContinuumStressRouteBoundary : Set where
  constructor continuum-stress-route-boundary
  field
    literalEq223MetricVariationAlreadyOwned : Bool
    r136StressRecoverySurfaceAlreadyOwned : Bool
    directFiniteContinuumResponseWeldRequired : Bool
    sourceVacuumIsraelAdmissionRequired : Bool
    fixedVacuumAmplitudePairRequired : Bool
    newIsraelGeometryRequired : Bool
    physicalContinuationCalibrationRequired : Bool

canonicalContinuumStressRouteBoundary : ContinuumStressRouteBoundary
canonicalContinuumStressRouteBoundary =
  continuum-stress-route-boundary
    true true true false false false true

------------------------------------------------------------------------
-- Explicit non-double-counting flags used by the live scheduler.
------------------------------------------------------------------------

thinWallVacuumRouteRequiresR136ResponseWeld : Bool
thinWallVacuumRouteRequiresR136ResponseWeld = false

continuumStressRouteRequiresSourceVacuumIsraelAdmission : Bool
continuumStressRouteRequiresSourceVacuumIsraelAdmission = false

sourceToGeometryAdmissionAndR136AreAlternativePayments : Bool
sourceToGeometryAdmissionAndR136AreAlternativePayments = true

finiteThicknessWallRequiredForThinWallClosure : Bool
finiteThicknessWallRequiredForThinWallClosure = false

sourceNativePotentialDynamicsRequiredForThinWallClosure : Bool
sourceNativePotentialDynamicsRequiredForThinWallClosure = false

------------------------------------------------------------------------
-- Honest remaining shortest-path leaves.
------------------------------------------------------------------------

record VacuumIsraelShortestPathLeaves : Set where
  constructor vacuum-israel-shortest-path-leaves
  field
    actualSelectedSourceVacuaLandInAdmissibleIsraelRegion : Bool
    physicalControlAndSICalibration : Bool
    experimentalRealisation : Bool

canonicalVacuumIsraelShortestPathLeaves : VacuumIsraelShortestPathLeaves
canonicalVacuumIsraelShortestPathLeaves =
  vacuum-israel-shortest-path-leaves true true true

record ContinuumStressShortestPathLeaves : Set where
  constructor continuum-stress-shortest-path-leaves
  field
    finiteEffectiveActionResponseIsSameR136Response : Bool
    euclideanLorentzianAndStressConventionCalibration : Bool
    physicalControlAndSICalibration : Bool
    experimentalRealisation : Bool

canonicalContinuumStressShortestPathLeaves : ContinuumStressShortestPathLeaves
canonicalContinuumStressShortestPathLeaves =
  continuum-stress-shortest-path-leaves true true true true

-- Existing source-native terminal remains the union-of-frontiers owner; this
-- module only corrects proof scheduling by exposing the disjunctive shortest
-- paths.  No source equality or physical admission is manufactured here.
sourceNativeReuseTerminalStillAuthoritativeUnion : Bool
sourceNativeReuseTerminalStillAuthoritativeUnion = true

sourceVacuumAdmissionSurfaceExists : Bool
sourceVacuumAdmissionSurfaceExists = true

r136ResponseWeldSurfaceExists : Bool
r136ResponseWeldSurfaceExists =
  Reuse.sameObjectEffectiveActionResponseWeldExists

noPhysicalPaymentPromotedByScheduler : Bool
noPhysicalPaymentPromotedByScheduler = true
