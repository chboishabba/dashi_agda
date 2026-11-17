{-# OPTIONS --safe #-}
module DASHI.Algebra.Trit.E8RootCountArithmeticExact where

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)

-- Counts of proposed coordinate/sign *choices* only.
-- No root membership, parity bijection, duplicate freedom or completeness.
coordinatePairs : Nat
coordinatePairs = 28

signChoicesPerPair : Nat
signChoicesPerPair = 4

integerChoiceCount : Nat
integerChoiceCount = coordinatePairs * signChoicesPerPair

evenParityHalfChoiceTarget : Nat
evenParityHalfChoiceTarget = 128

combinedChoiceCount : Nat
combinedChoiceCount = integerChoiceCount + evenParityHalfChoiceTarget

integerChoiceArithmetic : integerChoiceCount ≡ 112
integerChoiceArithmetic = refl

halfChoiceTargetArithmetic : evenParityHalfChoiceTarget ≡ 128
halfChoiceTargetArithmetic = refl

combinedChoiceArithmetic : combinedChoiceCount ≡ 240
combinedChoiceArithmetic = refl
