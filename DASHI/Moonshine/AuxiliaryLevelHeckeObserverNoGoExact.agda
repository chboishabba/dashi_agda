module DASHI.Moonshine.AuxiliaryLevelHeckeObserverNoGoExact where

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
-- David Blackwell,
-- "Equivalent Comparisons of Experiments", Annals of Mathematical Statistics
-- 24 (1953), 265--272. DOI: 10.1214/aoms/1177729032.
--
-- DASHI CONTRIBUTION
--
-- PR #585 reduces the observed p=11 Brandt-newform / deck-standard collision
-- from "try another prime" to a structural question: does the actual marked
-- carrier factor as
--
--     GlobalHeckeFactor x DeckFactor
--
-- with every prime-to-auxiliary-level Hecke correspondence acting only on the
-- global coordinate?
--
-- This file proves the exact observer consequence of that factorization.  If
-- the deck factor contains two distinct states, then:
--
--   * every individual Hecke readout collides on those states;
--   * every FINITE family of prime Hecke readouts still collides;
--   * even the pointwise ALL-prime family still collides;
--   * adding the deck coordinate is a strict observer refinement;
--   * (global, deck) is separating because it is the full marked coordinate.
--
-- Thus, once the same-object product factorization is proved geometrically,
-- blind prime-by-prime Hecke searching is impossible in principle rather than
-- merely unsuccessful through the currently scanned primes.
--
-- This is an observer theorem only.  It does NOT assert that the actual p=11
-- or p=37 marked carrier already satisfies the product factorization.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Moonshine.AuxiliaryLevelHeckeDeckFactorizationExact as Aux

------------------------------------------------------------------------
-- A concrete nontrivial deck fibre.
------------------------------------------------------------------------

record DistinctDeckWitness (F : Aux.AuxiliaryLevelHeckeFactorization) : Set where
  field
    deck0 deck1 : Aux.DeckState F
    deckDistinct : deck0 ≡ deck1 → ⊥

open DistinctDeckWitness public

------------------------------------------------------------------------
-- The global and deck observers on the actual product carrier.
------------------------------------------------------------------------

globalObserver :
  (F : Aux.AuxiliaryLevelHeckeFactorization) →
  Observer.Observer (Aux.MarkedState F) (Aux.GlobalState F)
globalObserver F marked = fst marked

deckObserver :
  (F : Aux.AuxiliaryLevelHeckeFactorization) →
  Observer.Observer (Aux.MarkedState F) (Aux.DeckState F)
deckObserver F marked = snd marked

primeHeckeObserver :
  (F : Aux.AuxiliaryLevelHeckeFactorization) →
  Aux.PrimeIndex F →
  Observer.Observer (Aux.MarkedState F) (Aux.GlobalState F)
primeHeckeObserver F ell = Aux.globalHeckeReadout F ell

------------------------------------------------------------------------
-- Every prime Hecke observer factors through the global projection.
------------------------------------------------------------------------

primeHeckeObserverFactorsThroughGlobal :
  (F : Aux.AuxiliaryLevelHeckeFactorization) →
  (ell : Aux.PrimeIndex F) →
  (marked : Aux.MarkedState F) →
  primeHeckeObserver F ell marked
  ≡ Aux.globalHecke F ell (globalObserver F marked)
primeHeckeObserverFactorsThroughGlobal F ell marked = refl

sameGlobalDifferentDeckPrimeCollision :
  (F : Aux.AuxiliaryLevelHeckeFactorization) →
  (ell : Aux.PrimeIndex F) →
  (global : Aux.GlobalState F) →
  (left right : Aux.DeckState F) →
  primeHeckeObserver F ell (global , left)
  ≡ primeHeckeObserver F ell (global , right)
sameGlobalDifferentDeckPrimeCollision F ell global left right = refl

------------------------------------------------------------------------
-- Any finite list of prime observers remains non-separating on a nontrivial
-- deck fibre.
------------------------------------------------------------------------

primeObserverFamily :
  (F : Aux.AuxiliaryLevelHeckeFactorization) →
  List (Aux.PrimeIndex F) →
  Observer.ObserverFamily (Aux.MarkedState F) (Aux.GlobalState F)
primeObserverFamily F [] = []
primeObserverFamily F (ell ∷ ells) =
  primeHeckeObserver F ell ∷ primeObserverFamily F ells

sameGlobalDifferentDeckAgreeOnPrimeList :
  (F : Aux.AuxiliaryLevelHeckeFactorization) →
  (ells : List (Aux.PrimeIndex F)) →
  (global : Aux.GlobalState F) →
  (left right : Aux.DeckState F) →
  Observer.AgreeOn
    (primeObserverFamily F ells)
    (global , left)
    (global , right)
sameGlobalDifferentDeckAgreeOnPrimeList F [] global left right = tt
sameGlobalDifferentDeckAgreeOnPrimeList F (ell ∷ ells) global left right =
  refl , sameGlobalDifferentDeckAgreeOnPrimeList F ells global left right

finitePrimeFamilyCannotSeparateDeck :
  (F : Aux.AuxiliaryLevelHeckeFactorization) →
  DistinctDeckWitness F →
  (ells : List (Aux.PrimeIndex F)) →
  (global : Aux.GlobalState F) →
  Observer.SeparatingFamily (primeObserverFamily F ells) →
  ⊥
finitePrimeFamilyCannotSeparateDeck F witness ells global separating =
  deckDistinct witness
    (cong snd
      (separating
        (global , deck0 witness)
        (global , deck1 witness)
        (sameGlobalDifferentDeckAgreeOnPrimeList
          F ells global (deck0 witness) (deck1 witness))))

------------------------------------------------------------------------
-- Stronger statement: even the entire pointwise prime family is blind.
-- No function extensionality is needed; agreement is indexed pointwise.
------------------------------------------------------------------------

AllPrimeAgreement :
  (F : Aux.AuxiliaryLevelHeckeFactorization) →
  Aux.MarkedState F → Aux.MarkedState F → Set
AllPrimeAgreement F left right =
  (ell : Aux.PrimeIndex F) →
  primeHeckeObserver F ell left ≡ primeHeckeObserver F ell right

AllPrimeSeparating :
  (F : Aux.AuxiliaryLevelHeckeFactorization) → Set
AllPrimeSeparating F =
  (left right : Aux.MarkedState F) →
  AllPrimeAgreement F left right →
  left ≡ right

sameGlobalDifferentDeckAgreeAtAllPrimes :
  (F : Aux.AuxiliaryLevelHeckeFactorization) →
  (global : Aux.GlobalState F) →
  (left right : Aux.DeckState F) →
  AllPrimeAgreement F (global , left) (global , right)
sameGlobalDifferentDeckAgreeAtAllPrimes F global left right ell = refl

allPrimeFamilyCannotSeparateDeck :
  (F : Aux.AuxiliaryLevelHeckeFactorization) →
  DistinctDeckWitness F →
  (global : Aux.GlobalState F) →
  AllPrimeSeparating F →
  ⊥
allPrimeFamilyCannotSeparateDeck F witness global separating =
  deckDistinct witness
    (cong snd
      (separating
        (global , deck0 witness)
        (global , deck1 witness)
        (sameGlobalDifferentDeckAgreeAtAllPrimes
          F global (deck0 witness) (deck1 witness))))

------------------------------------------------------------------------
-- Deck data is an exact strict refinement of the coarse global observer.
------------------------------------------------------------------------

globalObserverStrictlyRefinedByDeck :
  (F : Aux.AuxiliaryLevelHeckeFactorization) →
  DistinctDeckWitness F →
  (global : Aux.GlobalState F) →
  Observer.StrictRefinement
    (globalObserver F)
    (Observer.pairObserver (globalObserver F) (deckObserver F))
globalObserverStrictlyRefinedByDeck F witness global =
  Observer.strictPairRefinement
    (globalObserver F)
    (deckObserver F)
    (global , deck0 witness)
    (global , deck1 witness)
    refl
    (deckDistinct witness)

markedCoordinateObserverSeparating :
  (F : Aux.AuxiliaryLevelHeckeFactorization) →
  Observer.Separating
    (Observer.pairObserver (globalObserver F) (deckObserver F))
markedCoordinateObserverSeparating F (global0 , deck0') (global1 , deck1') same = same

------------------------------------------------------------------------
-- Boundary record: structural no-go is proved from factorization; actual
-- arithmetic carriers must still establish that factorization source-natively.
------------------------------------------------------------------------

record AuxiliaryHeckeObserverNoGoBoundary : Set where
  field
    finitePrimeBlindnessDerived : Bool
    finitePrimeBlindnessDerivedIsTrue : finitePrimeBlindnessDerived ≡ true

    allPrimeBlindnessDerived : Bool
    allPrimeBlindnessDerivedIsTrue : allPrimeBlindnessDerived ≡ true

    deckStrictRefinementDerived : Bool
    deckStrictRefinementDerivedIsTrue : deckStrictRefinementDerived ≡ true

    actualP11ProductFactorizationProvedHere : Bool
    actualP11ProductFactorizationProvedHereIsFalse :
      actualP11ProductFactorizationProvedHere ≡ false

canonicalAuxiliaryHeckeObserverNoGoBoundary : AuxiliaryHeckeObserverNoGoBoundary
canonicalAuxiliaryHeckeObserverNoGoBoundary = record
  { finitePrimeBlindnessDerived = true
  ; finitePrimeBlindnessDerivedIsTrue = refl
  ; allPrimeBlindnessDerived = true
  ; allPrimeBlindnessDerivedIsTrue = refl
  ; deckStrictRefinementDerived = true
  ; deckStrictRefinementDerivedIsTrue = refl
  ; actualP11ProductFactorizationProvedHere = false
  ; actualP11ProductFactorizationProvedHereIsFalse = refl
  }
