module DASHI.Moonshine.AuxiliaryLevelHeckeFactorizationAuthorityExact where

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
-- PR #585 has a persistent marked-Hecke/deck collision and a generic theorem:
-- IF the marked carrier source-natively factors as Global x Deck and all good
-- Hecke operators act only on Global, THEN the entire good-prime Hecke family
-- is blind to Deck.
--
-- The converse is not valid.  This file proves that failure constructively.
-- There is a finite marked Hecke system for which every prime/global readout is
-- blind to deck coordinates, while the actual Hecke action flips the deck.
-- Therefore observational all-prime collision cannot itself authorize the
-- product-factor / deck-preservation theorem.
--
-- This is the arithmetic instance of a repository-wide boundary also exposed
-- by the evidence/authority and observer-refinement lanes:
--
--     observed support / agreement != discharge of a structural obligation.
--
-- No claim is made that the toy system is arithmetic.  It is a falsifier of a
-- logically invalid inference rule.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Generic marked Hecke system before any factorization is assumed.
------------------------------------------------------------------------

record MarkedHeckeSystem : Set₁ where
  field
    GlobalState : Set
    DeckState : Set
    PrimeIndex : Set
    hecke : PrimeIndex → (GlobalState × DeckState) → (GlobalState × DeckState)

open MarkedHeckeSystem public

globalReadout :
  (S : MarkedHeckeSystem) →
  PrimeIndex S → GlobalState S × DeckState S → GlobalState S
globalReadout S ell marked = fst (hecke S ell marked)

AllPrimeGlobalBlindness : MarkedHeckeSystem → Set
AllPrimeGlobalBlindness S =
  (ell : PrimeIndex S) →
  (global : GlobalState S) →
  (deck0 deck1 : DeckState S) →
  globalReadout S ell (global , deck0)
  ≡ globalReadout S ell (global , deck1)

DeckPreserving : MarkedHeckeSystem → Set
DeckPreserving S =
  (ell : PrimeIndex S) →
  (global : GlobalState S) →
  (deck : DeckState S) →
  snd (hecke S ell (global , deck)) ≡ deck

------------------------------------------------------------------------
-- Structural authority is stronger than observational blindness.
------------------------------------------------------------------------

record ProductFactorAuthority (S : MarkedHeckeSystem) : Set where
  field
    deckPreserving : DeckPreserving S

open ProductFactorAuthority public

------------------------------------------------------------------------
-- Finite counterexample: the global coordinate is fixed but the deck flips.
------------------------------------------------------------------------

data ToyGlobal : Set where
  global0 : ToyGlobal

data ToyDeck : Set where
  deck0 deck1 : ToyDeck

data ToyPrime : Set where
  prime0 : ToyPrime

flipDeck : ToyDeck → ToyDeck
flipDeck deck0 = deck1
flipDeck deck1 = deck0

toyHecke : ToyPrime → ToyGlobal × ToyDeck → ToyGlobal × ToyDeck
toyHecke prime0 (global , deck) = global , flipDeck deck

toySystem : MarkedHeckeSystem
toySystem = record
  { GlobalState = ToyGlobal
  ; DeckState = ToyDeck
  ; PrimeIndex = ToyPrime
  ; hecke = toyHecke
  }

toyAllPrimeGlobalBlindness : AllPrimeGlobalBlindness toySystem
toyAllPrimeGlobalBlindness prime0 global left right = refl

deck1NotDeck0 : deck1 ≡ deck0 → ⊥
deck1NotDeck0 ()

toyNotDeckPreserving : DeckPreserving toySystem → ⊥
toyNotDeckPreserving preserving =
  deck1NotDeck0 (preserving prime0 global0 deck0)

toyHasNoProductFactorAuthority : ProductFactorAuthority toySystem → ⊥
toyHasNoProductFactorAuthority authority =
  toyNotDeckPreserving (deckPreserving authority)

------------------------------------------------------------------------
-- No universal inference may promote all-prime global blindness to product
-- factor authority.
------------------------------------------------------------------------

BlindnessToFactorizationPromoter : Set₁
BlindnessToFactorizationPromoter =
  (S : MarkedHeckeSystem) →
  AllPrimeGlobalBlindness S →
  ProductFactorAuthority S

allPrimeBlindnessCannotAuthorizeFactorization :
  BlindnessToFactorizationPromoter → ⊥
allPrimeBlindnessCannotAuthorizeFactorization promote =
  toyHasNoProductFactorAuthority
    (promote toySystem toyAllPrimeGlobalBlindness)

record AuxiliaryLevelHeckeFactorizationAuthorityBoundary : Set where
  field
    allPrimeBlindnessCounterexampleConstructed : Bool
    allPrimeBlindnessCounterexampleConstructedIsTrue :
      allPrimeBlindnessCounterexampleConstructed ≡ true

    blindnessDoesNotAuthorizeFactorization : Bool
    blindnessDoesNotAuthorizeFactorizationIsTrue :
      blindnessDoesNotAuthorizeFactorization ≡ true

    p11ProductFactorizationProvedHere : Bool
    p11ProductFactorizationProvedHereIsFalse :
      p11ProductFactorizationProvedHere ≡ false

canonicalAuxiliaryLevelHeckeFactorizationAuthorityBoundary :
  AuxiliaryLevelHeckeFactorizationAuthorityBoundary
canonicalAuxiliaryLevelHeckeFactorizationAuthorityBoundary = record
  { allPrimeBlindnessCounterexampleConstructed = true
  ; allPrimeBlindnessCounterexampleConstructedIsTrue = refl
  ; blindnessDoesNotAuthorizeFactorization = true
  ; blindnessDoesNotAuthorizeFactorizationIsTrue = refl
  ; p11ProductFactorizationProvedHere = false
  ; p11ProductFactorizationProvedHereIsFalse = refl
  }
