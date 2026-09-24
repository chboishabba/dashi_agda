module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseAtomisticCVProjectionValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseAtomisticCVProjectionExact as Projection

boundary = Projection.canonicalAdKAtomisticCVProjectionBoundary

_ : Projection.configurationToThreeCVMapInhabited boundary ≡ true
_ = refl

_ : Projection.sourceOwnedSelectionsRetained boundary ≡ true
_ = refl

_ : Projection.lowerConfigurationRetainedWithObservation boundary ≡ true
_ = refl

_ : Projection.rigidMotionInvarianceExposed boundary ≡ true
_ = refl

_ : Projection.threeCVObservationRecoversUniqueConfiguration boundary ≡ false
_ = refl

_ : Projection.threeCVObservationCreatesStateClassification boundary ≡ false
_ = refl
