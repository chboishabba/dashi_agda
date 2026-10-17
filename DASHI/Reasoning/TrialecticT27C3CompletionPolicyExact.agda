module DASHI.Reasoning.TrialecticT27C3CompletionPolicyExact where

------------------------------------------------------------------------
-- NATIVE C3 COMPLETION POLICY FOR THE T^18 -> T^27 GRAPH
--
-- The repository already owns an exact order-three participant C3 action on
-- ObserverMatrix3 SSPTrit.  Trialectic369HypervoxelUltrametricExact proves that
-- the observer matrix is exactly the same T^9 carrier as three T^3 hypervoxels.
--
-- This module transports that existing action to T9Coordinates and uses it as
-- an explicit structural completion policy
--
--   P_C3(firstNine , secondNine) = rho(firstNine).
--
-- It is a genuine inhabitant of T27CompletionPolicy and rho^3 = id exactly.
-- It is NOT identified with the IIT sibling's concrete B-operator graph law,
-- does not claim to use all T^18 information, and is not promoted to empirical
-- or physical dynamics.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Reasoning.TrialecticObserverMatrix369Exact as Observer
import DASHI.Reasoning.Trialectic369HypervoxelUltrametricExact as ExistingT9
import DASHI.Reasoning.Trialectic369DyadicC3LocalComplementSymmetryExact as ExistingC3
import DASHI.Reasoning.TrialecticT9T18T27GraphExtensionExact as Tower

------------------------------------------------------------------------
-- 1. Exact T^9 <-> observer-matrix rechart in the local neutral coordinates.
------------------------------------------------------------------------

t9ToObserver :
  Tower.T9Coordinates →
  Observer.ObserverMatrix3 SSP.SSPTrit
t9ToObserver
  (Tower.t9-coordinates
    (Fabric.ternary27Point aa ab ac)
    (Fabric.ternary27Point ba bb bc)
    (Fabric.ternary27Point ca cb cc)) =
  Observer.observerMatrix3
    aa ab ac
    ba bb bc
    ca cb cc

observerToT9 :
  Observer.ObserverMatrix3 SSP.SSPTrit →
  Tower.T9Coordinates
observerToT9
  (Observer.observerMatrix3
    aa ab ac
    ba bb bc
    ca cb cc) =
  Tower.t9-coordinates
    (Fabric.ternary27Point aa ab ac)
    (Fabric.ternary27Point ba bb bc)
    (Fabric.ternary27Point ca cb cc)

t9ObserverRoundTrip :
  (coordinates : Tower.T9Coordinates) →
  observerToT9 (t9ToObserver coordinates) ≡ coordinates
t9ObserverRoundTrip
  (Tower.t9-coordinates
    (Fabric.ternary27Point aa ab ac)
    (Fabric.ternary27Point ba bb bc)
    (Fabric.ternary27Point ca cb cc)) = refl

observerT9RoundTrip :
  (matrix : Observer.ObserverMatrix3 SSP.SSPTrit) →
  t9ToObserver (observerToT9 matrix) ≡ matrix
observerT9RoundTrip
  (Observer.observerMatrix3
    aa ab ac ba bb bc ca cb cc) = refl

t9ToObserverAgreesWithExistingBridge :
  (coordinates : Tower.T9Coordinates) →
  t9ToObserver coordinates
  ≡ ExistingT9.fabricToObserver
      (Fabric.ternaryHyperformalPoint
        (Tower.coordinate0 coordinates)
        (Tower.coordinate1 coordinates)
        (Tower.coordinate2 coordinates))
t9ToObserverAgreesWithExistingBridge
  (Tower.t9-coordinates
    (Fabric.ternary27Point aa ab ac)
    (Fabric.ternary27Point ba bb bc)
    (Fabric.ternary27Point ca cb cc)) = refl

------------------------------------------------------------------------
-- 2. Transport the existing participant C3 action onto T9Coordinates.
------------------------------------------------------------------------

rotateT9 : Tower.T9Coordinates → Tower.T9Coordinates
rotateT9
  (Tower.t9-coordinates
    (Fabric.ternary27Point aa ab ac)
    (Fabric.ternary27Point ba bb bc)
    (Fabric.ternary27Point ca cb cc)) =
  Tower.t9-coordinates
    (Fabric.ternary27Point bb bc ba)
    (Fabric.ternary27Point cb cc ca)
    (Fabric.ternary27Point ab ac aa)

rotateT9AgreesWithExistingC3 :
  (coordinates : Tower.T9Coordinates) →
  t9ToObserver (rotateT9 coordinates)
  ≡ ExistingC3.rotateABC (t9ToObserver coordinates)
rotateT9AgreesWithExistingC3
  (Tower.t9-coordinates
    (Fabric.ternary27Point aa ab ac)
    (Fabric.ternary27Point ba bb bc)
    (Fabric.ternary27Point ca cb cc)) = refl

rotateT9ThreeTimes :
  (coordinates : Tower.T9Coordinates) →
  rotateT9 (rotateT9 (rotateT9 coordinates)) ≡ coordinates
rotateT9ThreeTimes
  (Tower.t9-coordinates
    (Fabric.ternary27Point aa ab ac)
    (Fabric.ternary27Point ba bb bc)
    (Fabric.ternary27Point ca cb cc)) = refl

------------------------------------------------------------------------
-- 3. Concrete structural T^18 -> T^9 policy and completed T^27 graph.
------------------------------------------------------------------------

nativeC3CompletionPolicy : Tower.T27CompletionPolicy
nativeC3CompletionPolicy coordinates =
  rotateT9 (Tower.firstNine coordinates)

nativeC3CompletedCube :
  Tower.T18Coordinates → Tower.T27Coordinates
nativeC3CompletedCube = Tower.completeT27 nativeC3CompletionPolicy

nativeC3GraphLaw :
  (coordinates : Tower.T18Coordinates) →
  Tower.GraphLaw nativeC3CompletionPolicy (nativeC3CompletedCube coordinates)
nativeC3GraphLaw coordinates = refl

nativeC3ThirdFace :
  (coordinates : Tower.T18Coordinates) →
  Tower.face2 (nativeC3CompletedCube coordinates)
  ≡ rotateT9 (Tower.firstNine coordinates)
nativeC3ThirdFace coordinates = refl

nativeC3ProjectionRoundTrip :
  (coordinates : Tower.T18Coordinates) →
  Tower.projectT18 (nativeC3CompletedCube coordinates) ≡ coordinates
nativeC3ProjectionRoundTrip =
  Tower.projectCompleteT27 nativeC3CompletionPolicy

nativeC3ThirdFaceHasOrderThree :
  (coordinates : Tower.T18Coordinates) →
  rotateT9
    (rotateT9
      (rotateT9
        (Tower.face2 (nativeC3CompletedCube coordinates))))
  ≡ Tower.face2 (nativeC3CompletedCube coordinates)
nativeC3ThirdFaceHasOrderThree coordinates =
  rotateT9ThreeTimes (Tower.face2 (nativeC3CompletedCube coordinates))

------------------------------------------------------------------------
-- 4. Non-promotion boundaries.
------------------------------------------------------------------------

data NativeC3EqualsIITBOperatorPolicy : Set where
data NativeC3CompletionIsPhysicalDynamics : Set where

doNotIdentifyNativeC3WithIITBOperator :
  NativeC3EqualsIITBOperatorPolicy → ⊥
doNotIdentifyNativeC3WithIITBOperator ()

doNotPromoteNativeC3ToPhysicalDynamics :
  NativeC3CompletionIsPhysicalDynamics → ⊥
doNotPromoteNativeC3ToPhysicalDynamics ()

record TrialecticT27C3CompletionPolicyBoundary : Set where
  constructor trialectic-t27-c3-completion-policy-boundary
  field
    t9ObserverRechartExact : Bool
    existingParticipantC3ActionReused : Bool
    t9C3ActionOrderThree : Bool
    nativeC3CompletionPolicyConstructed : Bool
    nativeC3CompletionSatisfiesGraphLaw : Bool
    completedCubeProjectsExactlyToT18 : Bool
    completionPolicyUsesSecondT9Input : Bool
    iitBOperatorPolicyIdentifiedWithNativeC3 : Bool
    nativeC3PolicyPromotedToPhysicalDynamics : Bool

open TrialecticT27C3CompletionPolicyBoundary public

canonicalTrialecticT27C3CompletionPolicyBoundary :
  TrialecticT27C3CompletionPolicyBoundary
canonicalTrialecticT27C3CompletionPolicyBoundary =
  trialectic-t27-c3-completion-policy-boundary
    true true true true true true false false false
