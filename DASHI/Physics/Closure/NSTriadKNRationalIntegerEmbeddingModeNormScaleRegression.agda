module DASHI.Physics.Closure.NSTriadKNRationalIntegerEmbeddingModeNormScaleRegression where

------------------------------------------------------------------------
-- RED regression for S2b2c2a same-object lattice-normalization bridge.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNRationalIntegerEmbeddingModeNormScaleExact as Scale

integerEmbeddingCoordinateSquareScaleClosedIsTrue :
  Scale.integerEmbeddingCoordinateSquareScaleClosed ≡ true
integerEmbeddingCoordinateSquareScaleClosedIsTrue =
  Scale.integerEmbeddingCoordinateSquareScaleClosedIsTrue

modeNormCommonSquareScaleClosedIsTrue :
  Scale.modeNormCommonSquareScaleClosed ≡ true
modeNormCommonSquareScaleClosedIsTrue =
  Scale.modeNormCommonSquareScaleClosedIsTrue

shellGapTransportToLiveNormClosedIsTrue :
  Scale.shellGapTransportToLiveNormClosed ≡ true
shellGapTransportToLiveNormClosedIsTrue =
  Scale.shellGapTransportToLiveNormClosedIsTrue
