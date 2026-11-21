{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSVFObserverOSCyclicGramSetoidExact where

-- HIL07/HIL08: exact Gram-observational quotient transport.
-- The correct word quotient is indistinguishability against ALL tests,
-- not merely vanishing of a single cross-pairing. For positive
-- sesquilinear forms GNS null quotient requires additional physics.
-- No Hilbert completion, OS cyclic density or source Gram equality is
-- asserted as accomplished; equality is the explicit physical cut.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)

record MatchedPhysicalCyclicWords
    (ObserverWord OSWord Scalar : Set) : Set₁ where
  field
    observerPair : ObserverWord → ObserverWord → Scalar
    osPair : OSWord → OSWord → Scalar
    wordToOS : ObserverWord → OSWord
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

  ObserverEquivalent : ObserverWord → ObserverWord → Set
  ObserverEquivalent x y =
    (test : ObserverWord) →
    observerPair matched x test ≡ observerPair matched y test

  OSEquivalent : OSWord → OSWord → Set
  OSEquivalent x y =
    (test : OSWord) →
    osPair matched x test ≡ osPair matched y test

  observerReflexive : (x : ObserverWord) → ObserverEquivalent x x
  observerReflexive x test = refl

  observerSymmetric : (x y : ObserverWord) →
    ObserverEquivalent x y → ObserverEquivalent y x
  observerSymmetric x y proof test = sym (proof test)

  observerTransitive : (x y z : ObserverWord) →
    ObserverEquivalent x y → ObserverEquivalent y z →
    ObserverEquivalent x z
  observerTransitive x y z xy yz test =
    trans (xy test) (yz test)

  osReflexive : (x : OSWord) → OSEquivalent x x
  osReflexive x test = refl

  osSymmetric : (x y : OSWord) →
    OSEquivalent x y → OSEquivalent y x
  osSymmetric x y proof test = sym (proof test)

  osTransitive : (x y z : OSWord) →
    OSEquivalent x y → OSEquivalent y z →
    OSEquivalent x z
  osTransitive x y z xy yz test = trans (xy test) (yz test)

  originalEquivalentPairsMatchEveryMappedOSTest :
    (x y : ObserverWord) → ObserverEquivalent x y →
    (test : ObserverWord) →
    osPair matched (wordToOS matched x) (wordToOS matched test)
    ≡ osPair matched (wordToOS matched y) (wordToOS matched test)
  originalEquivalentPairsMatchEveryMappedOSTest x y proof test =
    trans (sym (allWordGramMatches matched x test))
      (trans (proof test) (allWordGramMatches matched y test))

  originalOSEquivalenceReflectsObserver :
    (x y : ObserverWord) →
    OSEquivalent (wordToOS matched x) (wordToOS matched y) →
    ObserverEquivalent x y
  originalOSEquivalenceReflectsObserver x y proof test =
    trans (allWordGramMatches matched x test)
      (trans (proof (wordToOS matched test))
        (sym (allWordGramMatches matched y test)))

  originalAllCyclicInnerProductsPreserved :
    (x y : ObserverWord) →
    observerPair matched x y
    ≡ osPair matched (wordToOS matched x) (wordToOS matched y)
  originalAllCyclicInnerProductsPreserved = allWordGramMatches matched

  -- Word-level OS coverage is a separate physical input. It is
  -- stronger than the Hilbert cyclic-density condition; eventually
  -- prove a dense range and extend by norm-completion instead.
  module _
      (osWordToObserver : OSWord → ObserverWord)
      (rightInverse : (word : OSWord) →
        wordToOS matched (osWordToObserver word) ≡ word)
    where

    originalEquivalencePreservedWithCoverage :
      (x y : ObserverWord) →
      ObserverEquivalent x y →
      OSEquivalent (wordToOS matched x) (wordToOS matched y)
    originalEquivalencePreservedWithCoverage x y proof test =
      trans
        (cong (osPair matched (wordToOS matched x))
          (sym (rightInverse test)))
        (trans
          (originalEquivalentPairsMatchEveryMappedOSTest
            x y proof (osWordToObserver test))
          (cong (osPair matched (wordToOS matched y))
            (rightInverse test)))

    originalOSWordCovered :
      (word : OSWord) →
      wordToOS matched (osWordToObserver word) ≡ word
    originalOSWordCovered = rightInverse

-- HIL01-05 still require the actual positive sesquilinear observer
-- state, nonzero quotient, complete complex Hilbert and Stone group.
-- HIL06-08 must derive allWordGramMatches from original TSVF/Wilson
-- and independent OS sources, plus a dense cyclic range. HIL09-11
-- still require full generator, spectral and Wick identifications.
