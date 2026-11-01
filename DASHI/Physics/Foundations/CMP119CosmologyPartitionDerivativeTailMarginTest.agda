{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPartitionDerivativeTailMarginTest where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.CMP119CosmologyPartitionDerivativeTailMarginExact as Subject

partitionDerivativeDominancePaysB2 :
  Subject.partitionDerivativeTailDominanceIsSufficientForB2 ≡ true
partitionDerivativeDominancePaysB2 = refl

connectedTraceNotRequired :
  Subject.connectedNormalizedTraceIsNotRequiredForB2 ≡ true
connectedTraceNotRequired = refl

sourceFacingB2IsOnePoint :
  Subject.sourceFacingB2IsOnePointPartitionResponse ≡ true
sourceFacingB2IsOnePoint = refl
