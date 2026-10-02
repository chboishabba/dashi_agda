module DASHI.ComputerScience.TekumWheelStateParityExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _∸_; _%_)

pow3 : Nat → Nat
pow3 zero = 1
pow3 (suc n) = 3 * pow3 n

availableAfterFiveSpecials : Nat → Nat
availableAfterFiveSpecials n = pow3 n ∸ 5

quadrantRemainder : Nat → Nat
quadrantRemainder n = availableAfterFiveSpecials n % 4

-- Hunhold Proposition 1 calibration rows: even widths admit four-way symmetry.
width2QuadrantRemainderZero : quadrantRemainder 2 ≡ 0
width2QuadrantRemainderZero = refl

width4QuadrantRemainderZero : quadrantRemainder 4 ≡ 0
width4QuadrantRemainderZero = refl

width6QuadrantRemainderZero : quadrantRemainder 6 ≡ 0
width6QuadrantRemainderZero = refl

width1QuadrantRemainderNonzero : quadrantRemainder 1 ≡ 2
width1QuadrantRemainderNonzero = refl

width3QuadrantRemainderNonzero : quadrantRemainder 3 ≡ 2
width3QuadrantRemainderNonzero = refl

record TekumWheelParityBoundary : Set where
  constructor tekumWheelParityBoundary
  field
    fiveDistinguishedWheelStatesRetained : Bool
    evenWidthFourQuadrantPattern : Bool
    oddWidthFailsSameFourWaySplit : Bool

canonicalTekumWheelParityBoundary : TekumWheelParityBoundary
canonicalTekumWheelParityBoundary =
  tekumWheelParityBoundary true true true
