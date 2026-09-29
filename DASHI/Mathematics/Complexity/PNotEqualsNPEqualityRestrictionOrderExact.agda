module DASHI.Mathematics.Complexity.PNotEqualsNPEqualityRestrictionOrderExact where

------------------------------------------------------------------------
-- RESTRICTION ORDER CAN COLLAPSE SEMANTIC QUOTIENT WIDTH
--
-- Companion:
--   PNotEqualsNPSemanticQuotientClassLowerBoundExact
--
-- Equality on two n-bit blocks has 2^n distinct residual subfunctions if all
-- first-block bits are fixed before the second block.
--
-- That exponential width is NOT intrinsic to the Boolean function.  Under the
-- interleaved order
--
--   x_1, y_1, x_2, y_2, ...
--
-- the residual semantics has only two states:
--
--   alive : all processed pairs agree; residual is equality on the suffix.
--   dead  : some processed pair disagreed; residual is constant false.
--
-- This owner proves the exact two-state factorization.
--
-- CONSEQUENCE FOR P9:
--
-- A good semantic quotient may come from a good decomposition/restriction
-- order.  The self-diagonal programme should therefore search not merely for a
-- quotient Q, but for a cheaply constructible decomposition order under which
-- the special self-instance family has small semantic width.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Vec.Base using (Vec; []; _∷_)

import DASHI.Mathematics.Complexity.PNotEqualsNPSemanticQuotientExponentialNoGoExact as Equality

------------------------------------------------------------------------
-- Two semantic states.
------------------------------------------------------------------------

data EqualityResidualState : Set where
  alive : EqualityResidualState
  dead : EqualityResidualState

advanceEqualityState :
  EqualityResidualState →
  Bool →
  Bool →
  EqualityResidualState
advanceEqualityState dead left right =
  dead
advanceEqualityState alive false false =
  alive
advanceEqualityState alive true true =
  alive
advanceEqualityState alive false true =
  dead
advanceEqualityState alive true false =
  dead

residualValue :
  ∀ {remaining : Nat} →
  EqualityResidualState →
  Vec Bool remaining →
  Vec Bool remaining →
  Bool
residualValue dead left right =
  false
residualValue alive left right =
  Equality.vecEq left right

------------------------------------------------------------------------
-- One interleaved pair update preserves exact semantics.
------------------------------------------------------------------------

residualStep :
  ∀ {remaining : Nat}
    (state : EqualityResidualState)
    (leftBit rightBit : Bool)
    (leftTail rightTail : Vec Bool remaining) →
  residualValue
    state
    (leftBit ∷ leftTail)
    (rightBit ∷ rightTail)
  ≡
  residualValue
    (advanceEqualityState state leftBit rightBit)
    leftTail
    rightTail
residualStep dead leftBit rightBit leftTail rightTail =
  refl
residualStep alive false false leftTail rightTail =
  refl
residualStep alive false true leftTail rightTail =
  refl
residualStep alive true false leftTail rightTail =
  refl
residualStep alive true true leftTail rightTail =
  refl

------------------------------------------------------------------------
-- Consume an interleaved prefix of matched positions.
------------------------------------------------------------------------

consumeEqualityPrefix :
  ∀ {processed : Nat} →
  EqualityResidualState →
  Vec Bool processed →
  Vec Bool processed →
  EqualityResidualState
consumeEqualityPrefix state [] [] =
  state
consumeEqualityPrefix
    state
    (leftBit ∷ leftBits)
    (rightBit ∷ rightBits) =
  consumeEqualityPrefix
    (advanceEqualityState state leftBit rightBit)
    leftBits
    rightBits

------------------------------------------------------------------------
-- Prefix/suffix recombination.
------------------------------------------------------------------------

appendVec :
  ∀ {leftLength rightLength : Nat} →
  Vec Bool leftLength →
  Vec Bool rightLength →
  Vec Bool (leftLength + rightLength)
appendVec [] right =
  right
appendVec (left ∷ lefts) right =
  left ∷ appendVec lefts right

interleavedPrefixFactorization :
  ∀ {processed remaining : Nat}
    (state : EqualityResidualState)
    (leftPrefix : Vec Bool processed)
    (rightPrefix : Vec Bool processed)
    (leftSuffix : Vec Bool remaining)
    (rightSuffix : Vec Bool remaining) →
  residualValue
    state
    (appendVec leftPrefix leftSuffix)
    (appendVec rightPrefix rightSuffix)
  ≡
  residualValue
    (consumeEqualityPrefix
      state
      leftPrefix
      rightPrefix)
    leftSuffix
    rightSuffix
interleavedPrefixFactorization
    state
    []
    []
    leftSuffix
    rightSuffix =
  refl
interleavedPrefixFactorization
    state
    (leftBit ∷ leftPrefix)
    (rightBit ∷ rightPrefix)
    leftSuffix
    rightSuffix =
  transitive
    (residualStep
      state
      leftBit
      rightBit
      (appendVec leftPrefix leftSuffix)
      (appendVec rightPrefix rightSuffix))
    (interleavedPrefixFactorization
      (advanceEqualityState state leftBit rightBit)
      leftPrefix
      rightPrefix
      leftSuffix
      rightSuffix)
  where
    transitive :
      ∀ {A : Set} {left middle right : A} →
      left ≡ middle →
      middle ≡ right →
      left ≡ right
    transitive refl refl =
      refl

------------------------------------------------------------------------
-- Equality itself factors through the two-state prefix machine.
------------------------------------------------------------------------

equalityFactorsThroughTwoStateInterleavedQuotient :
  ∀ {processed remaining : Nat}
    (leftPrefix : Vec Bool processed)
    (rightPrefix : Vec Bool processed)
    (leftSuffix : Vec Bool remaining)
    (rightSuffix : Vec Bool remaining) →
  Equality.vecEq
    (appendVec leftPrefix leftSuffix)
    (appendVec rightPrefix rightSuffix)
  ≡
  residualValue
    (consumeEqualityPrefix
      alive
      leftPrefix
      rightPrefix)
    leftSuffix
    rightSuffix
equalityFactorsThroughTwoStateInterleavedQuotient =
  interleavedPrefixFactorization alive

------------------------------------------------------------------------
-- Research consequence.
--
-- Block-order restriction:
--   2^n semantic residual classes.
--
-- Interleaved pair restriction:
--   exactly the two semantic states {alive, dead}.
--
-- Therefore semantic quotient width is decomposition-sensitive.  A viable P9
-- route for the SAT self-diagonal family may need to derive a special
-- restriction/decomposition order together with the quotient, rather than use
-- the inherited syntax-variable order.
------------------------------------------------------------------------
