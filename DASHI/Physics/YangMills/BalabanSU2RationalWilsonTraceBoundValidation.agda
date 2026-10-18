{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSU2RationalWilsonTraceBoundValidation where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; 1ℚ; -_; _≤_)

import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonTraceBoundExact as Bound

traceUpper :
  ∀ q → SU2.realPart q ≤ 1ℚ
traceUpper = Bound.normalizedTraceUpperBound

traceLower :
  ∀ q → - 1ℚ ≤ SU2.realPart q
traceLower = Bound.normalizedTraceLowerBound

traceInterval :
  ∀ q → Bound.RationalSU2NormalizedTraceBound q
traceInterval = Bound.normalizedTraceBound
