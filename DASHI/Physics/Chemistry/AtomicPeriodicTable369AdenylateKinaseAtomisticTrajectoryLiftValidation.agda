module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseAtomisticTrajectoryLiftValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseAtomisticTrajectoryLiftExact as Lift

boundary = Lift.canonicalAdKAtomisticTrajectoryLiftBoundary

_ : Lift.atomisticTrajectoryToCVTrajectoryDefined boundary ≡ true
_ = refl

_ : Lift.cvTrajectoryToStatePathDefined boundary ≡ true
_ = refl

_ : Lift.lowerFrameRetainedAtEveryProjection boundary ≡ true
_ = refl

_ : Lift.cvTrajectoryDeterminesUniqueAtomisticTrajectory boundary ≡ false
_ = refl

_ : Lift.statePathDeterminesUniqueCVTrajectory boundary ≡ false
_ = refl

_ : Lift.statePathCreatesPhysicalKinetics boundary ≡ false
_ = refl
