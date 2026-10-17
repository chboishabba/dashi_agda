module DASHI.Reasoning.TrialecticT27NativeC3AllDepthLiftExact where

------------------------------------------------------------------------
-- ALL-DEPTH LIFT OF THE STRUCTURED TRIALECTIC TRAJECTORY TO NATIVE-C3 T^27
--
-- TrialecticPolicyIndexedAllDepthIterationExact already proves that, once
-- mediation and expansion policies are supplied explicitly, every finite depth
-- has a structured T^18+face state.  The new native C3 completion policy can be
-- applied independently at each depth to the T^18 boundary of that state.
--
-- This produces a coherent observational lift
--
--   structured state_n
--      -> T^18(boundary_n)
--      -> CompletedT27(P_C3)_n
--
-- for every Nat depth.  Projection back to T^18 is exact at every depth and the
-- third T^9 face is exactly rho(firstNine).  The lift does NOT claim that the
-- completed T^27 state determines the next structured state, nor that the
-- structural trajectory is physical/empirical dynamics.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Cell
import DASHI.Reasoning.TrialecticPolicyIndexedAllDepthIterationExact as Depth
import DASHI.Reasoning.TrialecticT9T18T27GraphExtensionExact as Tower
import DASHI.Reasoning.TrialecticT27C3CompletionPolicyExact as C3Policy

structuredStateT18 : Cell.StructuredTrialecticState → Tower.T18Coordinates
structuredStateT18 state =
  Tower.compatibleBoundaryToT18 (Cell.structuredBoundary state)

structuredStateNativeC3T27 :
  Cell.StructuredTrialecticState →
  Tower.CompletedT27 C3Policy.nativeC3CompletionPolicy
structuredStateNativeC3T27 state =
  Tower.completedT27FromT18
    C3Policy.nativeC3CompletionPolicy
    (structuredStateT18 state)

structuredStateNativeProjectionExact :
  (state : Cell.StructuredTrialecticState) →
  Tower.projectT18
    (Tower.completedCube (structuredStateNativeC3T27 state))
  ≡ structuredStateT18 state
structuredStateNativeProjectionExact state =
  Tower.completedT27ProjectsExactly (structuredStateNativeC3T27 state)

structuredStateNativeThirdFaceExact :
  (state : Cell.StructuredTrialecticState) →
  Tower.face2
    (Tower.completedCube (structuredStateNativeC3T27 state))
  ≡ C3Policy.rotateT9 (Tower.firstNine (structuredStateT18 state))
structuredStateNativeThirdFaceExact state = refl

------------------------------------------------------------------------
-- Canonical all-depth trajectory inherited from the existing explicit-policy
-- recursion, now observed through the native-C3 completed graph at each depth.
------------------------------------------------------------------------

structuredTrajectory : Nat → Cell.StructuredTrialecticState
structuredTrajectory = Depth.canonicalAllDepthTrajectory

structuredTrajectoryT18 : Nat → Tower.T18Coordinates
structuredTrajectoryT18 depth =
  structuredStateT18 (structuredTrajectory depth)

nativeC3AllDepthTrajectory :
  Nat → Tower.CompletedT27 C3Policy.nativeC3CompletionPolicy
nativeC3AllDepthTrajectory depth =
  structuredStateNativeC3T27 (structuredTrajectory depth)

nativeC3TrajectoryProjectedT18 : Nat → Tower.T18Coordinates
nativeC3TrajectoryProjectedT18 depth =
  Tower.projectT18 (Tower.completedCube (nativeC3AllDepthTrajectory depth))

nativeC3TrajectoryProjectionExact :
  (depth : Nat) →
  nativeC3TrajectoryProjectedT18 depth ≡ structuredTrajectoryT18 depth
nativeC3TrajectoryProjectionExact depth =
  structuredStateNativeProjectionExact (structuredTrajectory depth)

nativeC3TrajectoryThirdFaceExact :
  (depth : Nat) →
  Tower.face2 (Tower.completedCube (nativeC3AllDepthTrajectory depth))
  ≡ C3Policy.rotateT9 (Tower.firstNine (structuredTrajectoryT18 depth))
nativeC3TrajectoryThirdFaceExact depth =
  structuredStateNativeThirdFaceExact (structuredTrajectory depth)

nativeC3TrajectoryThirdFaceOrderThree :
  (depth : Nat) →
  C3Policy.rotateT9
    (C3Policy.rotateT9
      (C3Policy.rotateT9
        (Tower.face2
          (Tower.completedCube (nativeC3AllDepthTrajectory depth)))))
  ≡ Tower.face2
      (Tower.completedCube (nativeC3AllDepthTrajectory depth))
nativeC3TrajectoryThirdFaceOrderThree depth =
  C3Policy.rotateT9ThreeTimes
    (Tower.face2 (Tower.completedCube (nativeC3AllDepthTrajectory depth)))

------------------------------------------------------------------------
-- Promotion boundaries.
------------------------------------------------------------------------

data CompletedT27DeterminesNextStructuredState : Set where
data AllDepthNativeC3LiftIsPhysicalDynamics : Set where

completedT27DoesNotDetermineNextStructuredState :
  CompletedT27DeterminesNextStructuredState → ⊥
completedT27DoesNotDetermineNextStructuredState ()

allDepthLiftDoesNotBecomePhysicalDynamics :
  AllDepthNativeC3LiftIsPhysicalDynamics → ⊥
allDepthLiftDoesNotBecomePhysicalDynamics ()

record TrialecticT27NativeC3AllDepthLiftBoundary : Set where
  constructor trialectic-t27-native-c3-all-depth-lift-boundary
  field
    everyFiniteDepthLiftedToNativeC3T27 : Bool
    everyDepthPreservesExactT18Projection : Bool
    everyDepthThirdFaceIsNativeC3Rotate : Bool
    everyDepthThirdFaceRetainsOrderThree : Bool
    existingExplicitPolicyIterationReused : Bool
    completedT27DeterminesNextStructuredState : Bool
    allDepthNativeC3LiftPromotedToPhysicalDynamics : Bool
    arbitraryInfinityDepthObjectClaimed : Bool

open TrialecticT27NativeC3AllDepthLiftBoundary public

canonicalTrialecticT27NativeC3AllDepthLiftBoundary :
  TrialecticT27NativeC3AllDepthLiftBoundary
canonicalTrialecticT27NativeC3AllDepthLiftBoundary =
  trialectic-t27-native-c3-all-depth-lift-boundary
    true true true true true false false false
