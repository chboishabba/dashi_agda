module DASHI.Arithmetic.FibonacciNonaryPeriodExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- D. D. Wall,
-- "Fibonacci Series Modulo m", The American Mathematical Monthly 67(6)
-- (1960), 525-532.
-- DOI: 10.1080/00029890.1960.11989541.
--
-- DASHI CONTRIBUTION
--
-- Work directly on the repository's cyclic NonaryTruth carrier.  The
-- Fibonacci companion map
--
--   (a,b) |-> (b,a+b mod 9)
--
-- returns the canonical start state (0,1) after 24 steps.  A complete
-- positive-offset scan proves that no offset 1..23 returns that state, so the
-- recurrence-state period modulo 9 is exactly 24.  The generic iterate-add
-- theorem then gives F_(n+24) = F_n on the nonary residue carrier.
--
-- On the canonical 24-cycle, the residues divisible by 3 occur exactly at
-- offsets 0,4,8,12,16,20.  This is the exact finite core behind the
-- Fibonacci/digital-root 3-6-9 observation; no decimal mysticism is assumed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import Base369 as Base

FibState9 : Set
FibState9 = Base.NonaryTruth × Base.NonaryTruth

fibStep : FibState9 → FibState9
fibStep (left , right) =
  right , Base.nonaryXor left right

iterate :
  {A : Set} →
  Nat → (A → A) → A → A
iterate zero step state = state
iterate (suc n) step state = step (iterate n step state)

iterateAdd :
  {A : Set} →
  (m n : Nat) →
  (step : A → A) →
  (state : A) →
  iterate (m + n) step state
  ≡ iterate m step (iterate n step state)
iterateAdd zero n step state = refl
iterateAdd (suc m) n step state =
  cong step (iterateAdd m n step state)

fibStart : FibState9
fibStart = Base.non-0 , Base.non-1

fibState : Nat → FibState9
fibState n = iterate n fibStep fibStart

fibResidue : Nat → Base.NonaryTruth
fibResidue n = proj₁ (fibState n)

fibStateAt24IsStart :
  fibState 24 ≡ fibStart
fibStateAt24IsStart = refl

fibStatePeriod24 :
  (n : Nat) →
  fibState (n + 24) ≡ fibState n
fibStatePeriod24 n =
  trans
    (iterateAdd n 24 fibStep fibStart)
    (cong (iterate n fibStep) fibStateAt24IsStart)

fibResiduePeriod24 :
  (n : Nat) →
  fibResidue (n + 24) ≡ fibResidue n
fibResiduePeriod24 n = cong proj₁ (fibStatePeriod24 n)

data PositiveOffsetBelow24 : Set where
  p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12
    p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 :
    PositiveOffsetBelow24

positiveOffsetNat : PositiveOffsetBelow24 → Nat
positiveOffsetNat p1 = 1
positiveOffsetNat p2 = 2
positiveOffsetNat p3 = 3
positiveOffsetNat p4 = 4
positiveOffsetNat p5 = 5
positiveOffsetNat p6 = 6
positiveOffsetNat p7 = 7
positiveOffsetNat p8 = 8
positiveOffsetNat p9 = 9
positiveOffsetNat p10 = 10
positiveOffsetNat p11 = 11
positiveOffsetNat p12 = 12
positiveOffsetNat p13 = 13
positiveOffsetNat p14 = 14
positiveOffsetNat p15 = 15
positiveOffsetNat p16 = 16
positiveOffsetNat p17 = 17
positiveOffsetNat p18 = 18
positiveOffsetNat p19 = 19
positiveOffsetNat p20 = 20
positiveOffsetNat p21 = 21
positiveOffsetNat p22 = 22
positiveOffsetNat p23 = 23

noPositiveOffsetBelow24StatePeriod :
  (offset : PositiveOffsetBelow24) →
  fibState (positiveOffsetNat offset) ≡ fibStart →
  ⊥
noPositiveOffsetBelow24StatePeriod p1 ()
noPositiveOffsetBelow24StatePeriod p2 ()
noPositiveOffsetBelow24StatePeriod p3 ()
noPositiveOffsetBelow24StatePeriod p4 ()
noPositiveOffsetBelow24StatePeriod p5 ()
noPositiveOffsetBelow24StatePeriod p6 ()
noPositiveOffsetBelow24StatePeriod p7 ()
noPositiveOffsetBelow24StatePeriod p8 ()
noPositiveOffsetBelow24StatePeriod p9 ()
noPositiveOffsetBelow24StatePeriod p10 ()
noPositiveOffsetBelow24StatePeriod p11 ()
noPositiveOffsetBelow24StatePeriod p12 ()
noPositiveOffsetBelow24StatePeriod p13 ()
noPositiveOffsetBelow24StatePeriod p14 ()
noPositiveOffsetBelow24StatePeriod p15 ()
noPositiveOffsetBelow24StatePeriod p16 ()
noPositiveOffsetBelow24StatePeriod p17 ()
noPositiveOffsetBelow24StatePeriod p18 ()
noPositiveOffsetBelow24StatePeriod p19 ()
noPositiveOffsetBelow24StatePeriod p20 ()
noPositiveOffsetBelow24StatePeriod p21 ()
noPositiveOffsetBelow24StatePeriod p22 ()
noPositiveOffsetBelow24StatePeriod p23 ()

data Offset24 : Set where
  o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12
    o13 o14 o15 o16 o17 o18 o19 o20 o21 o22 o23 : Offset24

offsetNat : Offset24 → Nat
offsetNat o0 = 0
offsetNat o1 = 1
offsetNat o2 = 2
offsetNat o3 = 3
offsetNat o4 = 4
offsetNat o5 = 5
offsetNat o6 = 6
offsetNat o7 = 7
offsetNat o8 = 8
offsetNat o9 = 9
offsetNat o10 = 10
offsetNat o11 = 11
offsetNat o12 = 12
offsetNat o13 = 13
offsetNat o14 = 14
offsetNat o15 = 15
offsetNat o16 = 16
offsetNat o17 = 17
offsetNat o18 = 18
offsetNat o19 = 19
offsetNat o20 = 20
offsetNat o21 = 21
offsetNat o22 = 22
offsetNat o23 = 23

isTriadicResidue : Base.NonaryTruth → Bool
isTriadicResidue Base.non-0 = true
isTriadicResidue Base.non-1 = false
isTriadicResidue Base.non-2 = false
isTriadicResidue Base.non-3 = true
isTriadicResidue Base.non-4 = false
isTriadicResidue Base.non-5 = false
isTriadicResidue Base.non-6 = true
isTriadicResidue Base.non-7 = false
isTriadicResidue Base.non-8 = false

isMultipleOfFourOffset : Offset24 → Bool
isMultipleOfFourOffset o0 = true
isMultipleOfFourOffset o1 = false
isMultipleOfFourOffset o2 = false
isMultipleOfFourOffset o3 = false
isMultipleOfFourOffset o4 = true
isMultipleOfFourOffset o5 = false
isMultipleOfFourOffset o6 = false
isMultipleOfFourOffset o7 = false
isMultipleOfFourOffset o8 = true
isMultipleOfFourOffset o9 = false
isMultipleOfFourOffset o10 = false
isMultipleOfFourOffset o11 = false
isMultipleOfFourOffset o12 = true
isMultipleOfFourOffset o13 = false
isMultipleOfFourOffset o14 = false
isMultipleOfFourOffset o15 = false
isMultipleOfFourOffset o16 = true
isMultipleOfFourOffset o17 = false
isMultipleOfFourOffset o18 = false
isMultipleOfFourOffset o19 = false
isMultipleOfFourOffset o20 = true
isMultipleOfFourOffset o21 = false
isMultipleOfFourOffset o22 = false
isMultipleOfFourOffset o23 = false

triadicPatternAtOffset :
  (offset : Offset24) →
  isTriadicResidue (fibResidue (offsetNat offset))
  ≡ isMultipleOfFourOffset offset
triadicPatternAtOffset o0 = refl
triadicPatternAtOffset o1 = refl
triadicPatternAtOffset o2 = refl
triadicPatternAtOffset o3 = refl
triadicPatternAtOffset o4 = refl
triadicPatternAtOffset o5 = refl
triadicPatternAtOffset o6 = refl
triadicPatternAtOffset o7 = refl
triadicPatternAtOffset o8 = refl
triadicPatternAtOffset o9 = refl
triadicPatternAtOffset o10 = refl
triadicPatternAtOffset o11 = refl
triadicPatternAtOffset o12 = refl
triadicPatternAtOffset o13 = refl
triadicPatternAtOffset o14 = refl
triadicPatternAtOffset o15 = refl
triadicPatternAtOffset o16 = refl
triadicPatternAtOffset o17 = refl
triadicPatternAtOffset o18 = refl
triadicPatternAtOffset o19 = refl
triadicPatternAtOffset o20 = refl
triadicPatternAtOffset o21 = refl
triadicPatternAtOffset o22 = refl
triadicPatternAtOffset o23 = refl

triadicStatusPeriod24 :
  (n : Nat) →
  isTriadicResidue (fibResidue (n + 24))
  ≡ isTriadicResidue (fibResidue n)
triadicStatusPeriod24 n =
  cong isTriadicResidue (fibResiduePeriod24 n)

record FibonacciNonaryBoundary : Set where
  field
    statePeriodTwentyFourProved : Bool
    statePeriodTwentyFourProvedIsTrue :
      statePeriodTwentyFourProved ≡ true
    noPositiveStatePeriodBelowTwentyFour : Bool
    noPositiveStatePeriodBelowTwentyFourIsTrue :
      noPositiveStatePeriodBelowTwentyFour ≡ true
    triadicOffsetsInCanonicalCycleAreMultiplesOfFour : Bool
    triadicOffsetsInCanonicalCycleAreMultiplesOfFourIsTrue :
      triadicOffsetsInCanonicalCycleAreMultiplesOfFour ≡ true

canonicalFibonacciNonaryBoundary : FibonacciNonaryBoundary
canonicalFibonacciNonaryBoundary =
  record
    { statePeriodTwentyFourProved = true
    ; statePeriodTwentyFourProvedIsTrue = refl
    ; noPositiveStatePeriodBelowTwentyFour = true
    ; noPositiveStatePeriodBelowTwentyFourIsTrue = refl
    ; triadicOffsetsInCanonicalCycleAreMultiplesOfFour = true
    ; triadicOffsetsInCanonicalCycleAreMultiplesOfFourIsTrue = refl
    }
