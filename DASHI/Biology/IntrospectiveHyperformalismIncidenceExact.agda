module DASHI.Biology.IntrospectiveHyperformalismIncidenceExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- INTROSPECTIVE V2: PIXEL-RECOVERED INCIDENCE / PATH STRUCTURE
--
-- A deterministic visualization was rendered from a finite hyperfabric model.
-- The OpenCV observer consumed only pixels, recovering:
--   4 large supervoxel rectangles,
--   9 fibre nodes with occupancy profile (3,1,2,3),
--   diamond incidence edges 0-1, 0-2, 1-3, 2-3,
--   two distinct length-two paths from 0 to 3.
--
-- Theorems below formalize only those recovered representation invariants.
------------------------------------------------------------------------

data ObservedSupervoxel : Set where
  s0 s1 s2 s3 : ObservedSupervoxel

observedFibreCount : ObservedSupervoxel → Nat
observedFibreCount s0 = 3
observedFibreCount s1 = 1
observedFibreCount s2 = 2
observedFibreCount s3 = 3

data ObservedEdge : ObservedSupervoxel → ObservedSupervoxel → Set where
  e01 : ObservedEdge s0 s1
  e02 : ObservedEdge s0 s2
  e13 : ObservedEdge s1 s3
  e23 : ObservedEdge s2 s3

data ObservedPath : ObservedSupervoxel → ObservedSupervoxel → Set where
  edgePath :
    ∀ {a b} → ObservedEdge a b → ObservedPath a b
  composePath :
    ∀ {a b c} → ObservedPath a b → ObservedPath b c → ObservedPath a c

upperRecoveredPath : ObservedPath s0 s3
upperRecoveredPath =
  composePath (edgePath e01) (edgePath e13)

lowerRecoveredPath : ObservedPath s0 s3
lowerRecoveredPath =
  composePath (edgePath e02) (edgePath e23)

data RecoveredRoute : Set where
  viaS1 viaS2 : RecoveredRoute

intermediateOf : RecoveredRoute → ObservedSupervoxel
intermediateOf viaS1 = s1
intermediateOf viaS2 = s2

distinctRecoveredIntermediateRoutes :
  intermediateOf viaS1 ≡ intermediateOf viaS2 → ⊥
distinctRecoveredIntermediateRoutes ()

recoveredContractedBranchIsOccupancyBottleneck :
  observedFibreCount s0 ≡ observedFibreCount s1 → ⊥
recoveredContractedBranchIsOccupancyBottleneck ()

recoveredReopenedBranchDiffersFromContracted :
  observedFibreCount s1 ≡ observedFibreCount s2 → ⊥
recoveredReopenedBranchDiffersFromContracted ()

recoveredStartAndGoalShareOccupancy :
  observedFibreCount s0 ≡ observedFibreCount s3
recoveredStartAndGoalShareOccupancy = refl

record IntrospectiveIncidenceBoundary : Set where
  constructor introspectiveIncidenceBoundary
  field
    cvRecoveredIncidenceNotOnlyCounts : Bool
    twoPixelPathsProveTwoBiologicalMechanisms : Bool
    visualBottleneckProvesClinicalEntrapment : Bool
    observerCanGenerateFormalPathObligations : Bool

canonicalIntrospectiveIncidenceBoundary : IntrospectiveIncidenceBoundary
canonicalIntrospectiveIncidenceBoundary =
  introspectiveIncidenceBoundary true false false true
