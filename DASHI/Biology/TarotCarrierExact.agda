module DASHI.Biology.TarotCarrierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Finite Rider--Waite--Smith tarot carrier.
--
-- Historical/source calibration:
-- * Pamela Colman Smith illustrated the deck published under Arthur Edward
--   Waite's direction in 1909.
-- * The 78-card carrier is 22 trumps plus four suits of fourteen cards.
-- * This file formalises the modern deck structure only.  It does not claim
--   an ancient Egyptian origin, fixed occult authority, or predictive power.
------------------------------------------------------------------------

data MajorArcana : Set where
  theFool theMagician theHighPriestess theEmpress theEmperor : MajorArcana
  theHierophant theLovers theChariot strength theHermit : MajorArcana
  wheelOfFortune justice theHangedMan death temperance : MajorArcana
  theDevil theTower theStar theMoon theSun judgement theWorld : MajorArcana

data Suit : Set where
  wands cups swords pentacles : Suit

data PipRank : Set where
  aceR twoR threeR fourR fiveR sixR sevenR eightR nineR tenR : PipRank

data CourtRank : Set where
  pageR knightR queenR kingR : CourtRank

data MinorRank : Set where
  pip : PipRank → MinorRank
  court : CourtRank → MinorRank

data Card : Set where
  major : MajorArcana → Card
  minor : Suit → MinorRank → Card

data Orientation : Set where
  uprightOrientation reversedOrientation : Orientation

data DeckTradition : Set where
  riderWaiteSmith marseille thoth : DeckTradition
  customTradition : String → DeckTradition

record CardToken : Set where
  constructor cardToken
  field
    cardIdentity : Card
    orientation : Orientation
    tradition : DeckTradition
    imageFeatureReceipts : List String

open CardToken public

------------------------------------------------------------------------
-- Explicit finite enumerations.
------------------------------------------------------------------------

allMajorArcana : List MajorArcana
allMajorArcana =
  theFool
  ∷ theMagician
  ∷ theHighPriestess
  ∷ theEmpress
  ∷ theEmperor
  ∷ theHierophant
  ∷ theLovers
  ∷ theChariot
  ∷ strength
  ∷ theHermit
  ∷ wheelOfFortune
  ∷ justice
  ∷ theHangedMan
  ∷ death
  ∷ temperance
  ∷ theDevil
  ∷ theTower
  ∷ theStar
  ∷ theMoon
  ∷ theSun
  ∷ judgement
  ∷ theWorld
  ∷ []

allSuits : List Suit
allSuits = wands ∷ cups ∷ swords ∷ pentacles ∷ []

allMinorRanks : List MinorRank
allMinorRanks =
  pip aceR
  ∷ pip twoR
  ∷ pip threeR
  ∷ pip fourR
  ∷ pip fiveR
  ∷ pip sixR
  ∷ pip sevenR
  ∷ pip eightR
  ∷ pip nineR
  ∷ pip tenR
  ∷ court pageR
  ∷ court knightR
  ∷ court queenR
  ∷ court kingR
  ∷ []

mapList : ∀ {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

infixr 5 _++L_

_++L_ : ∀ {A : Set} → List A → List A → List A
[] ++L ys = ys
(x ∷ xs) ++L ys = x ∷ (xs ++L ys)

listCount : ∀ {A : Set} → List A → Nat
listCount [] = 0
listCount (_ ∷ xs) = suc (listCount xs)

majorCards : List Card
majorCards = mapList major allMajorArcana

cardsOfSuit : Suit → List Card
cardsOfSuit suit = mapList (λ rank → minor suit rank) allMinorRanks

allCards : List Card
allCards =
  majorCards
  ++L cardsOfSuit wands
  ++L cardsOfSuit cups
  ++L cardsOfSuit swords
  ++L cardsOfSuit pentacles

majorArcanaCountIsTwentyTwo : listCount allMajorArcana ≡ 22
majorArcanaCountIsTwentyTwo = refl

suitCountIsFour : listCount allSuits ≡ 4
suitCountIsFour = refl

minorRankCountIsFourteen : listCount allMinorRanks ≡ 14
minorRankCountIsFourteen = refl

eachSuitCountIsFourteen : ∀ suit → listCount (cardsOfSuit suit) ≡ 14
eachSuitCountIsFourteen suit = refl

riderWaiteSmithDeckCountIsSeventyEight : listCount allCards ≡ 78
riderWaiteSmithDeckCountIsSeventyEight = refl

------------------------------------------------------------------------
-- Stable numeric indexing for draw-without-replacement witnesses.
------------------------------------------------------------------------

majorIndex : MajorArcana → Nat
majorIndex theFool = 0
majorIndex theMagician = 1
majorIndex theHighPriestess = 2
majorIndex theEmpress = 3
majorIndex theEmperor = 4
majorIndex theHierophant = 5
majorIndex theLovers = 6
majorIndex theChariot = 7
majorIndex strength = 8
majorIndex theHermit = 9
majorIndex wheelOfFortune = 10
majorIndex justice = 11
majorIndex theHangedMan = 12
majorIndex death = 13
majorIndex temperance = 14
majorIndex theDevil = 15
majorIndex theTower = 16
majorIndex theStar = 17
majorIndex theMoon = 18
majorIndex theSun = 19
majorIndex judgement = 20
majorIndex theWorld = 21

suitOffset : Suit → Nat
suitOffset wands = 22
suitOffset cups = 36
suitOffset swords = 50
suitOffset pentacles = 64

minorRankIndex : MinorRank → Nat
minorRankIndex (pip aceR) = 0
minorRankIndex (pip twoR) = 1
minorRankIndex (pip threeR) = 2
minorRankIndex (pip fourR) = 3
minorRankIndex (pip fiveR) = 4
minorRankIndex (pip sixR) = 5
minorRankIndex (pip sevenR) = 6
minorRankIndex (pip eightR) = 7
minorRankIndex (pip nineR) = 8
minorRankIndex (pip tenR) = 9
minorRankIndex (court pageR) = 10
minorRankIndex (court knightR) = 11
minorRankIndex (court queenR) = 12
minorRankIndex (court kingR) = 13

cardIndex : Card → Nat
cardIndex (major trump) = majorIndex trump
cardIndex (minor suit rank) = suitOffset suit + minorRankIndex rank

theFoolIndexIsZero : cardIndex (major theFool) ≡ 0
theFoolIndexIsZero = refl

theWorldIndexIsTwentyOne : cardIndex (major theWorld) ≡ 21
theWorldIndexIsTwentyOne = refl

kingOfPentaclesIndexIsSeventySeven :
  cardIndex (minor pentacles (court kingR)) ≡ 77
kingOfPentaclesIndexIsSeventySeven = refl

record TarotCarrierBoundary : Set where
  constructor tarotCarrierBoundary
  field
    seventyEightCardEnumerationProvided : Bool
    cardMeaningsIntrinsicContextFreeFacts : Bool
    orientationIntrinsicToPrintedCard : Bool
    deckTraditionsDefinitionallyIdentical : Bool

canonicalTarotCarrierBoundary : TarotCarrierBoundary
canonicalTarotCarrierBoundary =
  tarotCarrierBoundary true false false false
