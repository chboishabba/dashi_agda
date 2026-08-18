module DASHI.Moonshine.AuxiliaryLevelHeckeWordDeckCommutantExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John Voight,
-- "Quaternion Algebras", Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
--
-- DASHI CONTRIBUTION
--
-- PR #585 has reduced the marked-Hecke/deck collision to a same-object
-- auxiliary-level factorization question.  The earlier observer no-go proves
-- that individual good-prime readouts, finite prime families, and the whole
-- pointwise prime family cannot see a nontrivial deck fibre once
--
--      MarkedState = GlobalState x DeckState
--      T_ell(g,d) = (T_ell g,d).
--
-- This module closes the next algebraic loophole: COMPOSITIONS of good-prime
-- Hecke operators cannot recover the missing deck coordinate either.
--
-- We deliberately formalize the free MONOID of Hecke words, not the additive
-- Hecke algebra.  No additive module structure is silently inferred from a
-- product carrier.  The distinction follows the operator-role discipline now
-- independently emphasized by PR #587: Hecke action and deck action are
-- different operator roles, and their commutation is proved rather than
-- inferred from a shared carrier.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Moonshine.AuxiliaryLevelHeckeDeckFactorizationExact as Aux
import DASHI.Moonshine.AuxiliaryLevelHeckeObserverNoGoExact as PrimeNoGo

------------------------------------------------------------------------
-- Free word syntax and its source-shaped interpretation.
------------------------------------------------------------------------

data HeckeWord (F : Aux.AuxiliaryLevelHeckeFactorization) : Set where
  identity : HeckeWord F
  prime : Aux.PrimeIndex F → HeckeWord F
  _then_ : HeckeWord F → HeckeWord F → HeckeWord F

infixr 5 _then_

globalWordAction :
  (F : Aux.AuxiliaryLevelHeckeFactorization) →
  HeckeWord F → Aux.GlobalState F → Aux.GlobalState F
globalWordAction F identity global = global
globalWordAction F (prime ell) global = Aux.globalHecke F ell global
globalWordAction F (left then right) global =
  globalWordAction F right (globalWordAction F left global)

markedWordAction :
  (F : Aux.AuxiliaryLevelHeckeFactorization) →
  HeckeWord F → Aux.MarkedState F → Aux.MarkedState F
markedWordAction F word marked =
  globalWordAction F word (fst marked) , snd marked

wordGlobalReadout :
  (F : Aux.AuxiliaryLevelHeckeFactorization) →
  HeckeWord F → Aux.MarkedState F → Aux.GlobalState F
wordGlobalReadout F word marked = fst (markedWordAction F word marked)

------------------------------------------------------------------------
-- Every word preserves the deck coordinate exactly.
------------------------------------------------------------------------

wordPreservesDeck :
  (F : Aux.AuxiliaryLevelHeckeFactorization) →
  (word : HeckeWord F) →
  (marked : Aux.MarkedState F) →
  snd (markedWordAction F word marked) ≡ snd marked
wordPreservesDeck F word marked = refl

sameGlobalDifferentDeckWordCollision :
  (F : Aux.AuxiliaryLevelHeckeFactorization) →
  (word : HeckeWord F) →
  (global : Aux.GlobalState F) →
  (deck0 deck1 : Aux.DeckState F) →
  wordGlobalReadout F word (global , deck0)
  ≡ wordGlobalReadout F word (global , deck1)
sameGlobalDifferentDeckWordCollision F word global deck0 deck1 = refl

------------------------------------------------------------------------
-- Hecke words commute with EVERY deck-only endomorphism.  This is stronger
-- than one named S3 relation and needs no group law on DeckState.
------------------------------------------------------------------------

deckOnlyAction :
  (F : Aux.AuxiliaryLevelHeckeFactorization) →
  (Aux.DeckState F → Aux.DeckState F) →
  Aux.MarkedState F → Aux.MarkedState F
deckOnlyAction F deckMap marked = fst marked , deckMap (snd marked)

wordCommutesWithDeckOnlyAction :
  (F : Aux.AuxiliaryLevelHeckeFactorization) →
  (word : HeckeWord F) →
  (deckMap : Aux.DeckState F → Aux.DeckState F) →
  (marked : Aux.MarkedState F) →
  markedWordAction F word (deckOnlyAction F deckMap marked)
  ≡ deckOnlyAction F deckMap (markedWordAction F word marked)
wordCommutesWithDeckOnlyAction F word deckMap marked = refl

------------------------------------------------------------------------
-- Any finite family of Hecke WORD readouts is still non-separating on a
-- nontrivial deck fibre.
------------------------------------------------------------------------

wordObserver :
  (F : Aux.AuxiliaryLevelHeckeFactorization) →
  HeckeWord F →
  Observer.Observer (Aux.MarkedState F) (Aux.GlobalState F)
wordObserver F word = wordGlobalReadout F word

wordObserverFamily :
  (F : Aux.AuxiliaryLevelHeckeFactorization) →
  List (HeckeWord F) →
  Observer.ObserverFamily (Aux.MarkedState F) (Aux.GlobalState F)
wordObserverFamily F [] = []
wordObserverFamily F (word ∷ words) =
  wordObserver F word ∷ wordObserverFamily F words

sameGlobalDifferentDeckAgreeOnWords :
  (F : Aux.AuxiliaryLevelHeckeFactorization) →
  (words : List (HeckeWord F)) →
  (global : Aux.GlobalState F) →
  (deck0 deck1 : Aux.DeckState F) →
  Observer.AgreeOn
    (wordObserverFamily F words)
    (global , deck0)
    (global , deck1)
sameGlobalDifferentDeckAgreeOnWords F [] global deck0 deck1 = tt
sameGlobalDifferentDeckAgreeOnWords F (word ∷ words) global deck0 deck1 =
  refl , sameGlobalDifferentDeckAgreeOnWords F words global deck0 deck1

finiteWordFamilyCannotSeparateDeck :
  (F : Aux.AuxiliaryLevelHeckeFactorization) →
  PrimeNoGo.DistinctDeckWitness F →
  (words : List (HeckeWord F)) →
  (global : Aux.GlobalState F) →
  Observer.SeparatingFamily (wordObserverFamily F words) →
  ⊥
finiteWordFamilyCannotSeparateDeck F witness words global separating =
  PrimeNoGo.deckDistinct witness
    (cong snd
      (separating
        (global , PrimeNoGo.deck0 witness)
        (global , PrimeNoGo.deck1 witness)
        (sameGlobalDifferentDeckAgreeOnWords
          F words global
          (PrimeNoGo.deck0 witness)
          (PrimeNoGo.deck1 witness))))

------------------------------------------------------------------------
-- Even quantifying over ALL finite words pointwise cannot separate the deck.
------------------------------------------------------------------------

AllWordAgreement :
  (F : Aux.AuxiliaryLevelHeckeFactorization) →
  Aux.MarkedState F → Aux.MarkedState F → Set
AllWordAgreement F left right =
  (word : HeckeWord F) →
  wordGlobalReadout F word left ≡ wordGlobalReadout F word right

AllWordSeparating :
  (F : Aux.AuxiliaryLevelHeckeFactorization) → Set
AllWordSeparating F =
  (left right : Aux.MarkedState F) →
  AllWordAgreement F left right →
  left ≡ right

sameGlobalDifferentDeckAgreeAtAllWords :
  (F : Aux.AuxiliaryLevelHeckeFactorization) →
  (global : Aux.GlobalState F) →
  (deck0 deck1 : Aux.DeckState F) →
  AllWordAgreement F (global , deck0) (global , deck1)
sameGlobalDifferentDeckAgreeAtAllWords F global deck0 deck1 word = refl

allWordFamilyCannotSeparateDeck :
  (F : Aux.AuxiliaryLevelHeckeFactorization) →
  PrimeNoGo.DistinctDeckWitness F →
  (global : Aux.GlobalState F) →
  AllWordSeparating F →
  ⊥
allWordFamilyCannotSeparateDeck F witness global separating =
  PrimeNoGo.deckDistinct witness
    (cong snd
      (separating
        (global , PrimeNoGo.deck0 witness)
        (global , PrimeNoGo.deck1 witness)
        (sameGlobalDifferentDeckAgreeAtAllWords
          F global
          (PrimeNoGo.deck0 witness)
          (PrimeNoGo.deck1 witness))))

------------------------------------------------------------------------
-- Boundary: word closure is multiplicative/compositional only.  Additive
-- Hecke combinations and the actual p11 same-object factorization remain
-- distinct theorem obligations.
------------------------------------------------------------------------

record HeckeWordDeckBoundary : Set where
  field
    allFiniteWordFamiliesBlindToDeck : Bool
    allFiniteWordFamiliesBlindToDeckIsTrue :
      allFiniteWordFamiliesBlindToDeck ≡ true

    allWordsBlindToDeck : Bool
    allWordsBlindToDeckIsTrue : allWordsBlindToDeck ≡ true

    arbitraryDeckEndomorphismsCommuteWithWords : Bool
    arbitraryDeckEndomorphismsCommuteWithWordsIsTrue :
      arbitraryDeckEndomorphismsCommuteWithWords ≡ true

    additiveHeckeAlgebraConstructedHere : Bool
    additiveHeckeAlgebraConstructedHereIsFalse :
      additiveHeckeAlgebraConstructedHere ≡ false

    actualP11SameObjectFactorizationConstructedHere : Bool
    actualP11SameObjectFactorizationConstructedHereIsFalse :
      actualP11SameObjectFactorizationConstructedHere ≡ false

canonicalHeckeWordDeckBoundary : HeckeWordDeckBoundary
canonicalHeckeWordDeckBoundary = record
  { allFiniteWordFamiliesBlindToDeck = true
  ; allFiniteWordFamiliesBlindToDeckIsTrue = refl
  ; allWordsBlindToDeck = true
  ; allWordsBlindToDeckIsTrue = refl
  ; arbitraryDeckEndomorphismsCommuteWithWords = true
  ; arbitraryDeckEndomorphismsCommuteWithWordsIsTrue = refl
  ; additiveHeckeAlgebraConstructedHere = false
  ; additiveHeckeAlgebraConstructedHereIsFalse = refl
  ; actualP11SameObjectFactorizationConstructedHere = false
  ; actualP11SameObjectFactorizationConstructedHereIsFalse = refl
  }
