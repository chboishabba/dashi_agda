{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSVFObserverOSCyclicGramSetoidExact where

-- HIL07/HIL08 algebraic maximum-cut precursor.
-- An honest cyclic Gram equality gives quotient well-definedness and
-- exact preservation of all observable-word pairings; it is stronger
-- than merely matching two-point centered covariance.
--
-- The pairings, positivity, completion, and cyclic density must come
-- from the original observer and independently reconstructed physical
-- OS state. No field here asserts an onto Hilbert unitary.
--
-- Mathematical object constructed: a map of Gram-null setoids on
-- the ACTUAL source word carriers, with an inverse when a word-level
-- inverse is explicitly exhibited. This avoids quotient choice and
-- does NOT pretend an Agda setoid is already a complete Hilbert space.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality
  using (sym; trans; cong)

record MatchedPhysicalCyclicWords
    (ObserverWord OSWord Scalar : Set) : Set₁ where
  field
    zero : Scalar
    observerPair : ObserverWord → ObserverWord → Scalar
    osPair : OSWord → OSWord → Scalar
    wordToOS : ObserverWord → OSWord

    -- HIL07 physical producer: ALL words, not merely linear
    -- one/two-point jets. Must eventually be obtained from the
    -- same original Wilson/TSVF state and reconstructed OS state.
    allWordGramMatches :
      (left right : ObserverWord) →
      observerPair left right
      ≡ osPair (wordToOS left) (wordToOS right)

open MatchedPhysicalCyclicWords public

module _
    {ObserverWord OSWord Scalar : Set}
    (matched : MatchedPhysicalCyclicWords
      ObserverWord OSWord Scalar)
  where

  ObserverNull : ObserverWord → ObserverWord → Set
  ObserverNull left right =
    observerPair matched left right ≡ zero matched

  OSNull : OSWord → OSWord → Set
  OSNull left right =
    osPair matched left right ≡ zero matched

  -- Immediate mathematical gain: the selected physical Gram equality
  -- transports every null pair, so the cyclic map descends to the
  -- null-identified quotient without choosing representatives.
  originalGramNullMapsToOSNull :
    (left right : ObserverWord) →
    ObserverNull left right →
    OSNull (wordToOS matched left) (wordToOS matched right)
  originalGramNullMapsToOSNull left right evidence =
    trans (sym (allWordGramMatches matched left right)) evidence

  originalOSNullReflectsObserverNull :
    (left right : ObserverWord) →
    OSNull (wordToOS matched left) (wordToOS matched right) →
    ObserverNull left right
  originalOSNullReflectsObserverNull left right evidence =
    trans (allWordGramMatches matched left right) evidence

  originalNullEquivalence :
    (left right : ObserverWord) →
    ObserverNull left right →
    OSNull (wordToOS matched left) (wordToOS matched right)
  originalNullEquivalence = originalGramNullMapsToOSNull

  originalAllCyclicInnerProductsPreserved :
    (left right : ObserverWord) →
    observerPair matched left right
    ≡ osPair matched (wordToOS matched left) (wordToOS matched right)
  originalAllCyclicInnerProductsPreserved =
    allWordGramMatches matched

  -- A physical onto result cannot be inferred from an isometry.
  -- If the original independent OS word carrier is explicitly
  -- covered, the induced quotient has a two-sided inverse.
  module _
      (osWordToObserver : OSWord → ObserverWord)
      (rightInverse : (word : OSWord) →
        wordToOS matched (osWordToObserver word) ≡ word)
    where

    originalOSWordCoverage :
      (word : OSWord) →
      wordToOS matched (osWordToObserver word) ≡ word
    originalOSWordCoverage = rightInverse

    originalOSNullPullback :
      (left right : OSWord) →
      OSNull left right →
      ObserverNull (osWordToObserver left) (osWordToObserver right)
    originalOSNullPullback left right evidence =
      originalOSNullReflectsObserverNull
        (osWordToObserver left) (osWordToObserver right)
        (trans
          (cong
            (λ x → osPair matched x
              (wordToOS matched (osWordToObserver right)))
            (sym (rightInverse left)))
          (trans
            (cong (osPair matched left)
              (sym (rightInverse right)))
            evidence))

-- Physical interpretation of the remaining gap:
-- HIL01-05 require a positive sesquilinear observer functional,
-- a nonzero null quotient, its complex Hilbert completion and Stone.
-- HIL06-08 must prove allWordGramMatches from the *actual* same
-- Wilson/TSVF and OS sources, OS cyclic density and norm continuity.
-- HIL09-11 require real-time group/domain/spectrum/Wick semantics.
