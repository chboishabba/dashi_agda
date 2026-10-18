module DASHI.ComputerScience.TernarySignedDigitAdderSemanticsExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Vec using (Vec)

import DASHI.Algebra.Trit as Trit

------------------------------------------------------------------------
-- Hardware-independent semantic contract for redundant signed-digit adders.
-- Schlögl--Fey motivate a constant-depth FPGA implementation; correctness is a
-- separate theorem about the digit network.

record SignedDigitAdder (n : Nat) : Set₁ where
  field
    IntMeaning : Set
    Output : Set
    add : Vec Trit.Trit n → Vec Trit.Trit n → Output
    interpretedInput : Vec Trit.Trit n → IntMeaning
    interpretedOutput : Output → IntMeaning
    _+I_ : IntMeaning → IntMeaning → IntMeaning
    correct :
      (x y : Vec Trit.Trit n) →
      interpretedOutput (add x y)
      ≡ _+I_ (interpretedInput x) (interpretedInput y)

record AdderCostModel (n : Nat) : Set₁ where
  field
    Adder : SignedDigitAdder n
    lutCount : Nat
    criticalPathDepth : Nat

record SignedDigitAdderBoundary : Set where
  constructor signedDigitAdderBoundary
  field
    semanticCorrectnessSeparateFromTimingClaim : Bool
    signedDigitNetworkMayUseRedundantIntermediateDigits : Bool

canonicalSignedDigitAdderBoundary : SignedDigitAdderBoundary
canonicalSignedDigitAdderBoundary =
  signedDigitAdderBoundary true true
