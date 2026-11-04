{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21CookConsistencyComparisonClockExact where

------------------------------------------------------------------------
-- K00: FULL-SCAN NAT-INDEX COMPARISON ENVELOPE FOR THE ORIGINAL
-- COMPACT COOK SAT CERTIFICATE CHECKER.
--
-- Instrument the ACTUAL compatibleCookObservations rule and
-- allCookObservationsConsistent Boolean value. The two counted scans
-- are extensionally equal to those original verifier functions.
--
-- The exact scheduled number of Nat-index equality comparisons is
-- the sum of the remaining-tail lengths, bounded by k*k for k
-- syntactic variable observations. No dense max-variable-index
-- allocation occurs. This is an OPERATION COUNT, not a bit-tape clock:
-- the cost of comparing binary encoded Nat indices, parsing Cook
-- words, evaluation, and machine realization remains separate.
--
-- Sources: Stephen Cook (1971), Leonid Levin (1973), earlier DASHI
-- compact occurrence witness and actual Cook Boolean checker.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP
open import Data.Nat.Tactic.RingSolver using (solve-∀)

import DASHI.Mathematics.Complexity.Karp21BoolGoldenExact as Golden
import DASHI.Mathematics.Complexity.Karp21CookFiniteOccurrenceWitnessExact as Finite

-- The original compatibleCookObservations makes exactly one Nat-index
-- equality test for each explicit pair; schedule all pairs here.
countedAgainst :
  (Nat × Bool) → List (Nat × Bool) → Bool × Nat
countedAgainst observation [] = true , zero
countedAgainst observation (other ∷ rest) =
  let remaining = countedAgainst observation rest
  in (Golden.andBool
        (Finite.compatibleCookObservations observation other)
        (proj₁ remaining)
     , suc (proj₂ remaining))

countedAgainstValue :
  (observation : Nat × Bool) (rest : List (Nat × Bool)) →
  proj₁ (countedAgainst observation rest)
    ≡ Finite.oneCookObservationAgainst observation rest
countedAgainstValue observation [] = refl
countedAgainstValue observation (other ∷ rest)
  rewrite countedAgainstValue observation rest = refl

countedAgainstComparisons :
  (observation : Nat × Bool) (rest : List (Nat × Bool)) →
  proj₂ (countedAgainst observation rest) ≡ length rest
countedAgainstComparisons observation [] = refl
countedAgainstComparisons observation (other ∷ rest)
  rewrite countedAgainstComparisons observation rest = refl

-- Total pair count, once each pair of variable occurrences.
fullPairCount : List (Nat × Bool) → Nat
fullPairCount [] = zero
fullPairCount (_ ∷ rest) = length rest + fullPairCount rest

countedAll :
  List (Nat × Bool) → Bool × Nat
countedAll [] = true , zero
countedAll (observation ∷ rest) =
  let against = countedAgainst observation rest
      remaining = countedAll rest
  in (Golden.andBool (proj₁ against) (proj₁ remaining)
     , proj₂ against + proj₂ remaining)

countedAllValue :
  (observations : List (Nat × Bool)) →
  proj₁ (countedAll observations)
    ≡ Finite.allCookObservationsConsistent observations
countedAllValue [] = refl
countedAllValue (observation ∷ rest)
  rewrite countedAgainstValue observation rest
        | countedAllValue rest = refl

countedAllComparisons :
  (observations : List (Nat × Bool)) →
  proj₂ (countedAll observations) ≡ fullPairCount observations
countedAllComparisons [] = refl
countedAllComparisons (observation ∷ rest)
  rewrite countedAgainstComparisons observation rest
        | countedAllComparisons rest = refl

-- One induction, not a timing oracle. The linear tail count plus the
-- square bound for its suffix fits the next square, with positive slack.
squareStepRing :
  (k : Nat) →
  (k + (k * k)) + suc k ≡ suc k * suc k
squareStepRing = solve-∀

squareStepBound :
  (k : Nat) →
  k + (k * k) ≤ suc k * suc k
squareStepBound k =
  NatP.≤-trans
    (NatP.m≤m+n (k + (k * k)) (suc k))
    (NatP.≤-reflexive (squareStepRing k))

fullPairCountAtMostSquare :
  (observations : List (Nat × Bool)) →
  fullPairCount observations
    ≤ length observations * length observations
fullPairCountAtMostSquare [] = NatP.≤-refl
fullPairCountAtMostSquare (observation ∷ rest) =
  NatP.≤-trans
    (NatP.+-mono-≤ NatP.≤-refl
      (fullPairCountAtMostSquare rest))
    (squareStepBound (length rest))

k00ActualConsistencyComparisonEnvelope :
  (observations : List (Nat × Bool)) →
  proj₂ (countedAll observations)
    ≤ length observations * length observations
k00ActualConsistencyComparisonEnvelope observations
  rewrite countedAllComparisons observations =
  fullPairCountAtMostSquare observations

------------------------------------------------------------------------
-- The counted Boolean result is the exact ORIGINAL value. Its resource
-- bound does not itself inhabit PR.polynomialTimeVerifier for BitWord.
------------------------------------------------------------------------
