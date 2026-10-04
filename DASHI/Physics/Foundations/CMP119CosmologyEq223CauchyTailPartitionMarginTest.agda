{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyEq223CauchyTailPartitionMarginTest where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.CMP119CosmologyEq223CauchyTailPartitionMarginExact as Subject

cauchyPlusTailCoefficientMarginIsSufficient :
  Subject.cauchyPlusTailCoefficientMarginPaysPartitionB2 ≡ true
cauchyPlusTailCoefficientMarginIsSufficient = refl

partitionNormalizationNeedsNoSeparateEstimate :
  Subject.partitionNormalizationCancelsFromCauchyTailB2 ≡ true
partitionNormalizationNeedsNoSeparateEstimate = refl

connectedTraceNotUsed :
  Subject.connectedNormalizedResponseNotUsedInCauchyTailB2 ≡ true
connectedTraceNotUsed = refl
