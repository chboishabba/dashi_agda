{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.EinsteinEquationBidiResidualValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true)

import DASHI.Geometry.NonconstantWarpedLorentzianModel as Geometry
import DASHI.Physics.Closure.EinsteinEquationBidiResidualExact as Bidi

normalizedFiniteEinsteinAttemptPasses :
  Bidi.runEinsteinEquationAttempt Bidi.normalizedEightPiGCoupling
  ≡ Bidi.exactResidualZero
normalizedFiniteEinsteinAttemptPasses =
  Bidi.normalizedEquationAttemptPasses

wrongZeroCouplingIsRejected :
  Bidi.runEinsteinEquationAttempt Geometry.zeroUnit
  ≡ Bidi.nonzeroResidualCounterexample
wrongZeroCouplingIsRejected =
  Bidi.zeroCouplingAttemptFails

wrongNegativeCouplingIsRejected :
  Bidi.runEinsteinEquationAttempt Geometry.negativeUnit
  ≡ Bidi.nonzeroResidualCounterexample
wrongNegativeCouplingIsRejected =
  Bidi.negativeCouplingAttemptFails

calibrationRemainsOpen :
  Bidi.physicalCalibrationStillOpen ≡ true
calibrationRemainsOpen =
  Bidi.physicalCalibrationStillOpenIsTrue
