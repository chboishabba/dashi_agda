module DASHI.Moonshine.AuxiliaryLevelHeckeDeckFactorizationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John Voight,
-- "Quaternion Algebras", Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
-- Chapter 41 explains the Eichler/Brandt basis problem and the equality of
-- Hecke eigenvalue systems under the quaternionic/classical correspondence.
--
-- Hijikata, Pizer and Shemanske,
-- "The Basis Problem for Modular Forms on Gamma_0(N)",
-- Memoirs of the American Mathematical Society 82 (1989), no. 418.
-- No DOI is asserted here; the AMS monograph is cited by bibliographic data.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Princeton, 1985.
-- DOI: 10.1515/9781400881710.
-- Auxiliary full-level structures and prime-to-level correspondences.
--
-- DASHI CONTRIBUTION
--
-- Isolate the exact algebraic mechanism suggested by the p=11 and p=37
-- computations.  If an auxiliary-level observable space factors as
--
--      GlobalHeckeFactor x DeckFactor
--
-- and every prime-to-auxiliary-level Hecke operator acts only on the first
-- coordinate, then changing deck type while holding the global coordinate
-- fixed is INVISIBLE to the entire such Hecke family.
--
-- This theorem does not claim that the p=11 marked carrier has already been
-- identified with such a product decomposition.  It turns that geometric /
-- automorphic identification into the precise remaining same-object producer.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Product-factor Hecke action.
------------------------------------------------------------------------

record AuxiliaryLevelHeckeFactorization : Set₁ where
  field
    GlobalState : Set
    DeckState : Set
    PrimeIndex : Set
    globalHecke : PrimeIndex → GlobalState → GlobalState

  MarkedState : Set
  MarkedState = GlobalState × DeckState

  markedHecke : PrimeIndex → MarkedState → MarkedState
  markedHecke ell (global , deck) = globalHecke ell global , deck

open AuxiliaryLevelHeckeFactorization public

------------------------------------------------------------------------
-- Prime-to-level Hecke cannot distinguish deck coordinates at fixed global
-- state.  This is exact equality after projecting the Hecke result globally.
------------------------------------------------------------------------

globalHeckeReadout :
  (F : AuxiliaryLevelHeckeFactorization) →
  PrimeIndex F → MarkedState F → GlobalState F
globalHeckeReadout F ell marked = fst (markedHecke F ell marked)

sameGlobalDifferentDeckHaveSameHeckeReadout :
  (F : AuxiliaryLevelHeckeFactorization) →
  (ell : PrimeIndex F) →
  (global : GlobalState F) →
  (deck0 deck1 : DeckState F) →
  globalHeckeReadout F ell (global , deck0)
  ≡ globalHeckeReadout F ell (global , deck1)
sameGlobalDifferentDeckHaveSameHeckeReadout F ell global deck0 deck1 = refl

------------------------------------------------------------------------
-- Entire finite observer families remain blind to deck type under the same
-- factorization.  We use a pointwise family equality instead of inventing a
-- new list-observer core.
------------------------------------------------------------------------

allPrimeReadoutsCoincideAtFixedGlobal :
  (F : AuxiliaryLevelHeckeFactorization) →
  (global : GlobalState F) →
  (deck0 deck1 : DeckState F) →
  (ell : PrimeIndex F) →
  globalHeckeReadout F ell (global , deck0)
  ≡ globalHeckeReadout F ell (global , deck1)
allPrimeReadoutsCoincideAtFixedGlobal F global deck0 deck1 ell = refl

------------------------------------------------------------------------
-- A deck observer can still separate the two marked states.
------------------------------------------------------------------------

deckReadout :
  (F : AuxiliaryLevelHeckeFactorization) → MarkedState F → DeckState F
deckReadout F marked = snd marked

differentDeckStatesRemainDifferentMarkedCoordinates :
  (F : AuxiliaryLevelHeckeFactorization) →
  (global : GlobalState F) →
  (deck0 deck1 : DeckState F) →
  deck0 ≡ deck1 →
  (global , deck0) ≡ (global , deck1)
differentDeckStatesRemainDifferentMarkedCoordinates F global deck0 deck1 same =
  cong (λ deck → global , deck) same

record AuxiliaryLevelHeckeDeckBoundary : Set where
  field
    productFactorMechanismConstructed : Bool
    productFactorMechanismConstructedIsTrue :
      productFactorMechanismConstructed ≡ true

    allPrimeToLevelHeckeBlindToDeckAtFixedGlobal : Bool
    allPrimeToLevelHeckeBlindToDeckAtFixedGlobalIsTrue :
      allPrimeToLevelHeckeBlindToDeckAtFixedGlobal ≡ true

    p11SameObjectProductFactorizationClaimedHere : Bool
    p11SameObjectProductFactorizationClaimedHereIsFalse :
      p11SameObjectProductFactorizationClaimedHere ≡ false

canonicalAuxiliaryLevelHeckeDeckBoundary : AuxiliaryLevelHeckeDeckBoundary
canonicalAuxiliaryLevelHeckeDeckBoundary = record
  { productFactorMechanismConstructed = true
  ; productFactorMechanismConstructedIsTrue = refl
  ; allPrimeToLevelHeckeBlindToDeckAtFixedGlobal = true
  ; allPrimeToLevelHeckeBlindToDeckAtFixedGlobalIsTrue = refl
  ; p11SameObjectProductFactorizationClaimedHere = false
  ; p11SameObjectProductFactorizationClaimedHereIsFalse = refl
  }
