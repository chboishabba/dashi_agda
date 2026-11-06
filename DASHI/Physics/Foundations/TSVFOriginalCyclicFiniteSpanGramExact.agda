{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSVFOriginalCyclicFiniteSpanGramExact where

------------------------------------------------------------------------
-- HIL07 -> HIL08: exact finite real cyclic-span Gram compiler.
--
-- Extends a SAME-SOURCE equality of all original observer/OS word
-- Gram pairings to EVERY finite weighted superposition in the two
-- cyclic spans. Crucially uses the existing MatchedPhysicalCyclicWords
-- owner; there is no independent Gram-matching axiom, measure, or
-- observer functional introduced here.
--
-- This is formal finite-span bilinear algebra. It does NOT magically
-- give the true physical Hilbert linear combinations, complex
-- antilinearity, positivity, Cauchy completion, cyclic density, or
-- an onto unitary. Those require original operator and OS proofs.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong₂)

import DASHI.Physics.Foundations.TSVFObserverOSCyclicGramSetoidExact as Gram

module _
    {ObserverWord OSWord Scalar : Set}
    (zero : Scalar)
    (add multiply : Scalar → Scalar → Scalar)
    (matched : Gram.MatchedPhysicalCyclicWords
      ObserverWord OSWord Scalar)
  where

  ObserverSpan : Set
  ObserverSpan = List (Scalar × ObserverWord)

  OSSpan : Set
  OSSpan = List (Scalar × OSWord)

  mapCyclicSpan : ObserverSpan → OSSpan
  mapCyclicSpan [] = []
  mapCyclicSpan ((weight , word) ∷ rest) =
    (weight , Gram.wordToOS matched word) ∷ mapCyclicSpan rest

  observerRow : (Scalar × ObserverWord) → ObserverSpan → Scalar
  observerRow left [] = zero
  observerRow (a , x) ((b , y) ∷ right) =
    add (multiply (multiply a b) (Gram.observerPair matched x y))
        (observerRow (a , x) right)

  osRow : (Scalar × OSWord) → OSSpan → Scalar
  osRow left [] = zero
  osRow (a , x) ((b , y) ∷ right) =
    add (multiply (multiply a b) (Gram.osPair matched x y))
        (osRow (a , x) right)

  finiteObserverGram : ObserverSpan → ObserverSpan → Scalar
  finiteObserverGram [] right = zero
  finiteObserverGram (left ∷ rest) right =
    add (observerRow left right) (finiteObserverGram rest right)

  finiteOSGram : OSSpan → OSSpan → Scalar
  finiteOSGram [] right = zero
  finiteOSGram (left ∷ rest) right =
    add (osRow left right) (finiteOSGram rest right)

  -- Induction on each right span row, using the *original* pairwise
  -- word equality from the one selected matched source.
  originalAllFiniteRowGramMatches :
    (left : Scalar × ObserverWord) (right : ObserverSpan) →
    observerRow left right
    ≡ osRow (proj₁ left , Gram.wordToOS matched (proj₂ left))
        (mapCyclicSpan right)
  originalAllFiniteRowGramMatches left [] = refl
  originalAllFiniteRowGramMatches (a , x) ((b , y) ∷ rest) =
    cong₂ add
      (cong₂ multiply
        refl
        (Gram.allWordGramMatches matched x y))
      (originalAllFiniteRowGramMatches (a , x) rest)

  -- The first ORIGINAL all-cyclic-word Gram equality is now
  -- preserved by all finite real linear combinations, with no
  -- arbitrary test-family size bound and no extra pairwise axiom.
  originalAllFiniteSpanGramsMatch :
    (left right : ObserverSpan) →
    finiteObserverGram left right
    ≡ finiteOSGram (mapCyclicSpan left) (mapCyclicSpan right)
  originalAllFiniteSpanGramsMatch [] right = refl
  originalAllFiniteSpanGramsMatch (left ∷ rest) right =
    cong₂ add
      (originalAllFiniteRowGramMatches left right)
      (originalAllFiniteSpanGramsMatch rest right)

  -- In particular, every original finite-span self pairing is
  -- preserved. In a true positive OS Hilbert carrier this is the
  -- null-vector and isometry descent lemma; no positivity is
  -- introduced by this equality.
  originalAllFiniteSpanDiagonalMatches :
    (span : ObserverSpan) →
    finiteObserverGram span span
    ≡ finiteOSGram (mapCyclicSpan span) (mapCyclicSpan span)
  originalAllFiniteSpanDiagonalMatches span =
    originalAllFiniteSpanGramsMatch span span

-- To instantiate on the actual native Wilson/TSVF source use the
-- physical observer->R445 all-word cross-Gram theorem, and treat the
-- resulting finite coefficients as REAL until complex sesquilinear
-- and reflection/conjugation structure is independently constructed.
