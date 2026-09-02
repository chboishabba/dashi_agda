module DASHI.Moonshine.Base369MonsterThreeLocalEightToSixPlusTwoCarrierBidiExact where

------------------------------------------------------------------------
-- LITERAL 8 = 6 + 2 TERNARY-COORDINATE SPLIT
--
-- The existing Schrodinger model owns X6 = Trit^6.  The Base369 nonary owner
-- owns TritSquare = SSPTrit^2, with exact bridges between SSPTrit and Trit.
-- This file constructs a literal coordinate carrier
--
--   X8 ~= X6 x TritSquare,
--
-- making the arithmetic
--
--   3^8 = 3^6 * 3^2
--
-- a carrier-level product theorem.  It does NOT identify this X8 with the
-- sourced 3^8.Omega^-(8,3).2 module action; that still needs an equivariant
-- recognition receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Product using (_×_; _,_)
open import DASHI.Algebra.Trit using (Trit)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369NonaryTritSquareExact as Square
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H

record X8 : Set where
  constructor x8
  field
    x0 x1 x2 x3 x4 x5 x6 x7 : Trit
open X8 public

splitEight : X8 → H.X6 × Square.TritSquare
splitEight state =
  H.x6 (x0 state) (x1 state) (x2 state) (x3 state) (x4 state) (x5 state)
  , Square.tritSquare (SSP.fromTrit (x6 state)) (SSP.fromTrit (x7 state))

joinEight : H.X6 × Square.TritSquare → X8
joinEight
  ( six
  , Square.tritSquare high low
  ) =
  x8
    (H.x0 six) (H.x1 six) (H.x2 six)
    (H.x3 six) (H.x4 six) (H.x5 six)
    (SSP.toTrit high) (SSP.toTrit low)

joinAfterSplit : (state : X8) → joinEight (splitEight state) ≡ state
joinAfterSplit (x8 a b c d e f g h)
  rewrite SSP.toTrit-fromTrit g | SSP.toTrit-fromTrit h = refl

splitAfterJoin :
  (state : H.X6 × Square.TritSquare) →
  splitEight (joinEight state) ≡ state
splitAfterJoin
  (H.x6 a b c d e f , Square.tritSquare g h)
  rewrite SSP.fromTrit-toTrit g | SSP.fromTrit-toTrit h = refl

threePowerEight : Nat
threePowerEight = 3 * 3 * 3 * 3 * 3 * 3 * 3 * 3

threePowerSixTimesThreeSquared : Nat
threePowerSixTimesThreeSquared = 729 * (3 * 3)

threePowerEightIs6561 : threePowerEight ≡ 6561
threePowerEightIs6561 = refl

sixPlusTwoProductIs6561 : threePowerSixTimesThreeSquared ≡ 6561
sixPlusTwoProductIs6561 = refl

tenTimesEightCarrierDimension : Nat
tenTimesEightCarrierDimension = 10 * threePowerEight

tenTimesEightCarrierIs65610 : tenTimesEightCarrierDimension ≡ 65610
tenTimesEightCarrierIs65610 = refl

record EightToSixPlusTwoActionRecognition (Actor : Set) : Set₁ where
  field
    x8Act : Actor → X8 → X8
    x6SquareAct : Actor → (H.X6 × Square.TritSquare) → (H.X6 × Square.TritSquare)
    splitIntertwines :
      (actor : Actor) →
      (state : X8) →
      splitEight (x8Act actor state) ≡ x6SquareAct actor (splitEight state)
open EightToSixPlusTwoActionRecognition public

record EightToSixPlusTwoBoundary : Set where
  constructor eightToSixPlusTwoBoundary
  field
    literalEightCoordinateCarrierConstructed : Bool
    literalSixPlusTwoProductChartConstructed : Bool
    sixCoordinatesReuseHeisenbergX6 : Bool
    twoCoordinatesReuseBase369TritSquare : Bool
    arithmeticThreePowerEightRefactorGenerated : Bool
    carrierSplitIdentifiesThreePowerEightMonsterAction : Bool
    equivariantRecognitionStillRequired : Bool

canonicalEightToSixPlusTwoBoundary : EightToSixPlusTwoBoundary
canonicalEightToSixPlusTwoBoundary =
  eightToSixPlusTwoBoundary true true true true true false true
