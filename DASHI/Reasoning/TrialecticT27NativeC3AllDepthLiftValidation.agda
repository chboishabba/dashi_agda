module DASHI.Reasoning.TrialecticT27NativeC3AllDepthLiftValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Reasoning.TrialecticT27NativeC3AllDepthLiftExact as Lift

boundary : Lift.TrialecticT27NativeC3AllDepthLiftBoundary
boundary = Lift.canonicalTrialecticT27NativeC3AllDepthLiftBoundary

allDepthLiftPaid : Lift.everyFiniteDepthLiftedToNativeC3T27 boundary ≡ true
allDepthLiftPaid = refl

projectionPaid : Lift.everyDepthPreservesExactT18Projection boundary ≡ true
projectionPaid = refl

thirdFacePaid : Lift.everyDepthThirdFaceIsNativeC3Rotate boundary ≡ true
thirdFacePaid = refl

notNextStateDynamics : Lift.completedT27DeterminesNextStructuredState boundary ≡ false
notNextStateDynamics = refl

notPhysical : Lift.allDepthNativeC3LiftPromotedToPhysicalDynamics boundary ≡ false
notPhysical = refl

projectionAtEveryDepth :
  (depth : Nat) →
  Lift.nativeC3TrajectoryProjectedT18 depth
  ≡ Lift.structuredTrajectoryT18 depth
projectionAtEveryDepth = Lift.nativeC3TrajectoryProjectionExact
