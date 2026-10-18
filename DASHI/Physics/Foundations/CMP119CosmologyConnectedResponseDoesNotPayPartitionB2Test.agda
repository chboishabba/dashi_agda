{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyConnectedResponseDoesNotPayPartitionB2Test where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.CMP119CosmologyConnectedResponseDoesNotPayPartitionB2Exact as Subject

connectedResponseDoesNotDeterminePartitionDerivative :
  Subject.connectedNormalizedResponseDoesNotDeterminePartitionDerivative ≡ true
connectedResponseDoesNotDeterminePartitionDerivative = refl

orderedHaarConnectedTraceDoesNotPayB2 :
  Subject.orderedHaarConnectedTraceCannotDirectlyPayCosmologyB2 ≡ true
orderedHaarConnectedTraceDoesNotPayB2 = refl
