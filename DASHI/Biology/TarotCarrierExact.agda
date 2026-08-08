module DASHI.Biology.TarotCarrierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

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

allMajorArcana : List MajorArcana
allMajorArcana =
  theFool ∷ theMagician ∷ theHighPriestess ∷ theEmpress ∷ theEmperor
  ∷ theHierophant ∷ theLovers ∷ theChariot ∷ strength ∷ theHermit
  ∷ wheelOfFortune ∷ justice ∷ theHangedMan ∷ death ∷ temperance
  ∷ theDevil ∷ theTower ∷ theStar ∷ theMoon ∷ theSun ∷ judgement ∷ theWorld ∷ []

listCount : ∀ {A : Set} → List A → Nat
listCount [] = 0
listCount (_ ∷ xs) = suc (listCount xs)

majorArcanaCountIsTwentyTwo : listCount allMajorArcana ≡ 22
majorArcanaCountIsTwentyTwo = refl

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
