module DASHI.Physics.Closure.NSTriadKNHHBadPositiveThresholdRound58 where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_; _≤_; _<_) 

record PositiveThreshold : Set where
  constructor positive-threshold
  field
    threshold thresholdInverse : ℚ
    thresholdPositive : 0ℚ < threshold
    thresholdInverseNonnegative : 0ℚ ≤ thresholdInverse
    inverseMeaning : thresholdInverse * threshold ≡ 1ℚ

open PositiveThreshold public
