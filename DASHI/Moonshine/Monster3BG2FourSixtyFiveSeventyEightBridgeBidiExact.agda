module DASHI.Moonshine.Monster3BG2FourSixtyFiveSeventyEightBridgeBidiExact where

------------------------------------------------------------------------
-- G2(4) BRIDGE TARGET FOR THE SUZ 143 / WILSON 12+78 TRIANGLE
--
-- Source-backed subgroup spine:
--
--   G2(4)          < Suz
--   3 x G2(4)      < 3.Suz
--   3 x 2.G2(4)    < 6.Suz
--
-- Wilson's 3B restriction uses faithful degrees
--
--   143 on Suz,
--    78 on 3.Suz,
--    12 on 6.Suz.
--
-- Therefore the correct next object is not a bare degree coincidence but a
-- COVER-COHERENT branching triangle over the common G2(4) spine.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Sum.Base using (_⊎_)

sixtyFivePlusSeventyEight : 65 + 78 ≡ 143
sixtyFivePlusSeventyEight = refl

twelvePlusSeventyEight : 12 + 78 ≡ 90
twelvePlusSeventyEight = refl

------------------------------------------------------------------------
-- 1. Ordinary Suz -> G2(4) branch target.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- 2. Cover-level restriction receipts.
--
-- These remain abstract until the CTblLib producer identifies the concrete
-- faithful degree-78 / degree-12 characters and their exact restrictions.
------------------------------------------------------------------------

record ThreeSuzSeventyEightRestriction : Set₁ where
  field
    ThreeSuz78 ThreeTimesG2Four78 : Set
    restrict78 : ThreeSuz78 → ThreeTimesG2Four78
    lift78 : ThreeTimesG2Four78 → ThreeSuz78
    liftAfterRestrict78 : (x : ThreeSuz78) → lift78 (restrict78 x) ≡ x
    restrictAfterLift78 : (x : ThreeTimesG2Four78) → restrict78 (lift78 x) ≡ x
    dimension78 : Nat
    dimension78Is78 : dimension78 ≡ 78

record SixSuzTwelveRestriction : Set₁ where
  field
    SixSuz12 ThreeTimesTwoG2Four12 : Set
    restrict12 : SixSuz12 → ThreeTimesTwoG2Four12
    lift12 : ThreeTimesTwoG2Four12 → SixSuz12
    liftAfterRestrict12 : (x : SixSuz12) → lift12 (restrict12 x) ≡ x
    restrictAfterLift12 : (x : ThreeTimesTwoG2Four12) → restrict12 (lift12 x) ≡ x
    dimension12 : Nat
    dimension12Is12 : dimension12 ≡ 12

------------------------------------------------------------------------
-- 3. Same-78 weld target.
--
-- Even after 143|G2(4)=65+78 and the 3.Suz cover restriction are certified,
-- matching degree is insufficient.  A valid promotion identifies the G2(4)
-- 78 from the Suz-143 branch with the actual Wilson multiplicity-78 object on
-- the SAME restricted subgroup action.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- 4. Boundary / epistemic status.
------------------------------------------------------------------------

record G2FourBridgeBoundary : Set where
  constructor g2FourBridgeBoundary
  field
    g2FourMaximalInSuzSourceBacked : Bool
    threeTimesG2FourInThreeSuzSourceBacked : Bool
    threeTimesTwoG2FourInSixSuzSourceBacked : Bool
    g2FourHasOrdinary65SourceBacked : Bool
    g2FourHasOrdinary78SourceBacked : Bool
    arithmetic65Plus78Is143 : Bool
    ordinarySuz143RestrictionTo65Plus78CertifiedHere : Bool
    WilsonMultiplicity78SourceBacked : Bool
    threeSuz78CoverRestrictionCertifiedHere : Bool
    sixSuz12CoverRestrictionCertifiedHere : Bool
    matchingDegree78ProvesSameRepresentation : Bool
    sameObjectWilson78G2FourWeldInhabitedHere : Bool
    Albert53ShouldRemainHighestPriority : Bool

canonicalG2FourBridgeBoundary : G2FourBridgeBoundary
canonicalG2FourBridgeBoundary =
  g2FourBridgeBoundary
    true true true
    true true true
    false
    true
    false false
    false false
    false

------------------------------------------------------------------------
-- Target diagram after the executable branch receipts close:
--
--                 Suz_143
--                 /     \
--              65        78_G2
--                          ? same object
--                          |
--      3.Suz_78 ------> 3 x G2(4)
--                          |
--                     Wilson 78
--                          |
--                     12 + 78 = 90
--                          |
--      6.Suz_12 ------> 3 x 2.G2(4)
--
-- This is a cover-coherent G2(4) spine, not a degree-only identification.
------------------------------------------------------------------------
