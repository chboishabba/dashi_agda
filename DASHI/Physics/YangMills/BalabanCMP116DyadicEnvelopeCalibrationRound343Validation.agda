{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116DyadicEnvelopeCalibrationRound343Validation where

-- RED regression surface for Round343.
-- The concrete direct producer should replace a pointwise source-envelope to
-- spectrum-envelope premise by a dyadic shell identity, distance=time, and one
-- amplitude comparison.

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.YangMills.BalabanCMP116DyadicEnvelopeCalibrationRound343Exact as R343

genericPointwiseEnvelopeComparisonNotPrimitive :
  R343.pointwiseEnvelopeComparisonPrimitive ≡ false
genericPointwiseEnvelopeComparisonNotPrimitive =
  R343.pointwiseEnvelopeComparisonPrimitiveIsFalse

dyadicCalibrationCompilesR342 :
  R343.dyadicCalibrationBuildsR342Source ≡ true
dyadicCalibrationCompilesR342 =
  R343.dyadicCalibrationBuildsR342SourceIsTrue

onlyAmplitudeDistanceShellCoordinatesRemain :
  R343.dyadicCalibrationUsesOnlyShellDistanceAmplitude ≡ true
onlyAmplitudeDistanceShellCoordinatesRemain =
  R343.dyadicCalibrationUsesOnlyShellDistanceAmplitudeIsTrue
