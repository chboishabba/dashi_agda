module DASHI.Biology.IntrospectiveSymmetryResolvedHyperformalismExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- INTROSPECTIVE V3: FORMALIZE WHAT THE PIXEL OBSERVER RECOVERED
--
-- Producer:
--   scripts/introspective_embodied_hyperfabric_v3.py
--
-- The OpenCV observer recovered, from pixels only after rendering:
--   supervoxel occupancy       = 3,1,2,3
--   incidence                  = 0-1,0-2,1-3,2-3
--   S1 vector samples          = 4, div proxy ~ +3.995, curl ~ 0
--   S2 vector samples          = 4, div proxy ~ 0, curl ~ +3.995
--   S1 orientation             = ~0 degrees
--   S2 orientation             = ~44.3 degrees
--   S1 gate                    = open-outline
--   S2 gate                    = closed-filled
--
-- This module categoricalizes those robust recovered distinctions.  It does
-- not formalize the renderer's intended biology, nor infer cortical mechanism
-- or phenomenal state from the image.
------------------------------------------------------------------------

data ObservedSupervoxel : Set where
  s0 s1 s2 s3 : ObservedSupervoxel

observedFibreCount : ObservedSupervoxel → Nat
observedFibreCount s0 = 3
observedFibreCount s1 = 1
observedFibreCount s2 = 2
observedFibreCount s3 = 3

data ObservedEdge : ObservedSupervoxel → ObservedSupervoxel → Set where
  edge01 : ObservedEdge s0 s1
  edge02 : ObservedEdge s0 s2
  edge13 : ObservedEdge s1 s3
  edge23 : ObservedEdge s2 s3

data RecoveredGeometry : Set where
  sourceLikeRecovered rotationalLikeRecovered : RecoveredGeometry

data RecoveredChirality : Set where
  neutralChirality positiveChirality : RecoveredChirality

data RecoveredOrientation : Set where
  nearHorizontal nearDiagonal : RecoveredOrientation

data RecoveredGate : Set where
  openOutline closedFilled : RecoveredGate

record RecoveredModeObservation : Set where
  constructor recoveredModeObservation
  field
    atSupervoxel : ObservedSupervoxel
    vectorSampleCount : Nat
    geometry : RecoveredGeometry
    chirality : RecoveredChirality
    orientation : RecoveredOrientation
    gate : RecoveredGate

open RecoveredModeObservation public

sourceObservation : RecoveredModeObservation
sourceObservation =
  recoveredModeObservation s1 4 sourceLikeRecovered neutralChirality nearHorizontal openOutline

rotationalObservation : RecoveredModeObservation
rotationalObservation =
  recoveredModeObservation s2 4 rotationalLikeRecovered positiveChirality nearDiagonal closedFilled

recoveredGeometryDiffers :
  geometry sourceObservation ≡ geometry rotationalObservation → ⊥
recoveredGeometryDiffers ()

recoveredChiralityDiffers :
  chirality sourceObservation ≡ chirality rotationalObservation → ⊥
recoveredChiralityDiffers ()

recoveredOrientationDiffers :
  orientation sourceObservation ≡ orientation rotationalObservation → ⊥
recoveredOrientationDiffers ()

recoveredGateDiffers :
  gate sourceObservation ≡ gate rotationalObservation → ⊥
recoveredGateDiffers ()

recoveredIntermediateOccupancyDiffers :
  observedFibreCount s1 ≡ observedFibreCount s2 → ⊥
recoveredIntermediateOccupancyDiffers ()

record SymmetryIntrospectionBoundary : Set where
  constructor symmetryIntrospectionBoundary
  field
    pixelObserverRecoveredModeGeometry : Bool
    pixelObserverRecoveredGateDifference : Bool
    pixelGeometryProvesNeuralMechanism : Bool
    pixelGateProvesClinicalEntrapment : Bool
    pixelModeProvesPhenomenalConsciousness : Bool

canonicalSymmetryIntrospectionBoundary : SymmetryIntrospectionBoundary
canonicalSymmetryIntrospectionBoundary =
  symmetryIntrospectionBoundary true true false false false
