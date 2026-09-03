module DASHI.Moonshine.Monster3BG2FourSixtyFiveSeventyEightBridgeBidiExact where

------------------------------------------------------------------------
-- G2(4) BRIDGE TARGET FOR THE SUZ 143 AND WILSON 78
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Sum.Base using (_⊎_)

sixtyFivePlusSeventyEight : 65 + 78 ≡ 143
sixtyFivePlusSeventyEight = refl

twelvePlusSeventyEight : 12 + 78 ≡ 90
twelvePlusSeventyEight = refl

record Suz143ToG2FourBranching : Set₁ where
  field
    Suz143Carrier G2SixtyFiveCarrier G2SeventyEightCarrier : Set

    restrict143 : Suz143Carrier → G2SixtyFiveCarrier ⊎ G2SeventyEightCarrier
    combine143 : G2SixtyFiveCarrier ⊎ G2SeventyEightCarrier → Suz143Carrier

    combineAfterRestrict :
      (state : Suz143Carrier) → combine143 (restrict143 state) ≡ state
    restrictAfterCombine :
      (state : G2SixtyFiveCarrier ⊎ G2SeventyEightCarrier) →
      restrict143 (combine143 state) ≡ state

    sixtyFiveDimension : Nat
    seventyEightDimension : Nat
    sixtyFiveDimensionIs65 : sixtyFiveDimension ≡ 65
    seventyEightDimensionIs78 : seventyEightDimension ≡ 78

open Suz143ToG2FourBranching public

record WilsonSeventyEightG2FourSameObject
    (branch : Suz143ToG2FourBranching) : Set₁ where
  field
    Wilson78 Actor : Set
    g2SeventyEightAct : Actor → G2SeventyEightCarrier branch → G2SeventyEightCarrier branch
    wilsonSeventyEightAct : Actor → Wilson78 → Wilson78

    toWilson78 : G2SeventyEightCarrier branch → Wilson78
    fromWilson78 : Wilson78 → G2SeventyEightCarrier branch

    fromAfterTo :
      (state : G2SeventyEightCarrier branch) →
      fromWilson78 (toWilson78 state) ≡ state
    toAfterFrom :
      (state : Wilson78) →
      toWilson78 (fromWilson78 state) ≡ state

    intertwines :
      (actor : Actor) →
      (state : G2SeventyEightCarrier branch) →
      toWilson78 (g2SeventyEightAct actor state)
      ≡ wilsonSeventyEightAct actor (toWilson78 state)

open WilsonSeventyEightG2FourSameObject public

record G2FourBridgeBoundary : Set where
  constructor g2FourBridgeBoundary
  field
    g2FourMaximalInSuzSourceBacked : Bool
    g2FourHasOrdinary65SourceBacked : Bool
    g2FourHasOrdinary78SourceBacked : Bool
    arithmetic65Plus78Is143 : Bool
    ordinarySuz143RestrictionTo65Plus78CertifiedHere : Bool
    WilsonMultiplicity78SourceBacked : Bool
    matchingDegree78ProvesSameRepresentation : Bool
    sameObjectWilson78G2FourWeldInhabitedHere : Bool
    Albert53ShouldRemainHighestPriority : Bool

canonicalG2FourBridgeBoundary : G2FourBridgeBoundary
canonicalG2FourBridgeBoundary =
  g2FourBridgeBoundary
    true true true true
    false
    true
    false false
    false

------------------------------------------------------------------------
-- Interpretation if the executable branch test closes:
--
--          Suz 143
--          /     \
--       65        78_G2
--                  ?
--                  |
--              78_Wilson
--                  |
--             12 + 78 = 90
--
-- Matching degree does not identify the two 78s.  The second promotion needs
-- an actual shared subgroup/cover action and an intertwiner.
------------------------------------------------------------------------
