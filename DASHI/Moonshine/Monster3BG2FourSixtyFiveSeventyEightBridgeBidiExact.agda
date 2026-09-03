module DASHI.Moonshine.Monster3BG2FourSixtyFiveSeventyEightBridgeBidiExact where

------------------------------------------------------------------------
-- G2(4) BRIDGE TARGET FOR THE SUZ 143 AND WILSON 78
--
-- Published/source-backed data now gives three distinct structures:
--
--   (1) Suz has a faithful irreducible character of degree 143.
--   (2) G2(4) is a maximal subgroup of Suz and has ordinary irreducibles of
--       degrees 65 and 78.
--   (3) Wilson's Monster 3B restriction contains a degree-78 multiplicity
--       constituent paired with degree 12 inside the nontrivial central phase.
--
-- The highest-priority branching test is therefore
--
--     143 |_ G2(4) ?= 65 + 78.
--
-- Even if that equality is certified by CTblLib, it does NOT by itself prove
-- that the G2(4)-degree-78 constituent is the same representation object as
-- Wilson's degree-78 multiplicity constituent.  The latter lives in the
-- central-extension/inertia tower of the 3B normalizer.  A second same-object
-- / cover-character weld is required.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

------------------------------------------------------------------------
-- 1. Arithmetic shadows.
------------------------------------------------------------------------

sixtyFivePlusSeventyEight : 65 + 78 ≡ 143
sixtyFivePlusSeventyEight = refl

twelvePlusSeventyEight : 12 + 78 ≡ 90
twelvePlusSeventyEight = refl

------------------------------------------------------------------------
-- 2. Exact ordinary branching receipt.
--
-- This record is deliberately agnostic about concrete character-table APIs.
-- The executable producer `scripts/suz_143_subgroup_restriction_probe.g`
-- supplies the actual CTblLib test.  Once generated data is imported, this
-- record can be inhabited by the certified G2(4) restriction.
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
-- 3. Same-78 weld target.
--
-- Degree equality is insufficient.  A valid promotion identifies the
-- G2(4)-78 carrier with the ACTUAL Wilson multiplicity-78 carrier and proves
-- that both carry the same selected subgroup action after restriction.
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
-- This would connect the fixed central-trivial side and the nontrivial-phase
-- multiplicity side through G2(4), without reviving the forbidden Suz-stable
-- 143 = 90 + 53 split.
------------------------------------------------------------------------
