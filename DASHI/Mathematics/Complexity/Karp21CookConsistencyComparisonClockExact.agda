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
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Data.Maybe.Base using (just)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Mathematics.Complexity.Karp21BoolGoldenExact as Golden
import DASHI.Mathematics.Complexity.Karp21CookFiniteOccurrenceWitnessExact as Finite
import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.Karp21CookStrictTripleBitBoundaryExact as Strict
import DASHI.Mathematics.Complexity.Karp21CookExecutableFiniteVerifierBidiExact as Verifier
import DASHI.Mathematics.Complexity.Karp21CookAllWordCertificateBoundExact as AllWords

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

------------------------------------------------------------------------
-- P0 SAME ACCEPTED BITWORD: k observations fit in the certificate
-- bits, and the original K00 all-word theorem bounds accepted
-- certificates by the actual strict SAT input word.
--
-- The arithmetic thus gives an explicit quadratic comparison
-- envelope in the length of THAT original word. It is not a
-- bit-tape transition count and is not a PolynomialCostModel witness.
------------------------------------------------------------------------

pairObservationsNoLongerThanBits :
  (indices : List Nat) (bits : List Bool) →
  length (Finite.pairObservations indices bits) ≤ length bits
pairObservationsNoLongerThanBits [] bits = z≤n
pairObservationsNoLongerThanBits (_ ∷ rest) [] = z≤n
pairObservationsNoLongerThanBits (_ ∷ rest) (_ ∷ bits) =
  s≤s (pairObservationsNoLongerThanBits rest bits)

k00ActualAcceptedWordPairComparisonBound :
  (word bits : Word.BitWord)
  (formula : Cook.BooleanFormula) →
  Strict.strictDecodeCookFormulaBits word ≡ just formula →
  Verifier.verifyStrictCookSATWord word bits ≡ true →
  proj₂
    (countedAll
      (Finite.pairObservations
        (Finite.formulaVariables formula) bits))
    ≤ Word.encodingSize word * Word.encodingSize word
k00ActualAcceptedWordPairComparisonBound word bits formula decoded checked =
  let observations =
        Finite.pairObservations (Finite.formulaVariables formula) bits
      observationsWithinWord =
        NatP.≤-trans
          (pairObservationsNoLongerThanBits
            (Finite.formulaVariables formula) bits)
          (NatP.≤-trans
            (NatP.≤-reflexive
              (sym (Finite.canonicalBitWordIsListLength bits)))
            (AllWords.k00StrictAcceptedWordCertificateBound
              word bits checked))
  in NatP.≤-trans
      (k00ActualConsistencyComparisonEnvelope observations)
      (NatP.*-mono-≤
        observationsWithinWord observationsWithinWord)
