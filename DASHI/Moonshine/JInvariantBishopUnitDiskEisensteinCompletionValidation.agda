module DASHI.Moonshine.JInvariantBishopUnitDiskEisensteinCompletionValidation where

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Moonshine.JInvariantBishopUnitDiskEisensteinCompletionExact as P

unitDiskCompletionRegression :
  ∀ {q ratio} →
  (input : P.BishopUnitDiskQ q ratio) →
  P.BishopUnitDiskEisensteinCompletion q ratio input
unitDiskCompletionRegression =
  P.completeBishopUnitDiskEisenstein
