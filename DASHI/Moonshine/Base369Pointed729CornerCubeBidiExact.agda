module DASHI.Moonshine.Base369Pointed729CornerCubeBidiExact where

------------------------------------------------------------------------
-- GEOMETRIC CORNER WELD FOR THE POINTED 729 DECOMPOSITION
--
-- The pointed-appraisal owner already had
--
--   PointedAppraisal729 ~= (Fin 8 x (10 x 9)) + 9.
--
-- Base369Ternary27CornerEightExact identifies that same Fin 8 with the literal
-- eight corners of the existing 3x3x3 ternary cube.  This owner therefore
-- upgrades the address-level factor to
--
--   PointedAppraisal729
--      ~= (Corner(T^3) x (10 x 3^2)) + 3^2.
--
-- This is a literal carrier theorem.  No Monster action is inferred from the
-- geometry; an action-level corner interpretation still needs intertwining.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Product using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

import DASHI.Foundations.Base369PointedAppraisalFibreExact as Pointed
import DASHI.Foundations.Base369Ternary27CornerEightExact as Corners
import DASHI.Moonshine.Base369Monster3BMultiplicityTenByNineBidiExact as Ninety
import DASHI.Moonshine.Base369Pointed729NestedNinetyBidiExact as Nested

CornerIndexed729 : Set
CornerIndexed729 =
  (Corners.Corner3 × Ninety.TenByNineMultiplicity)
  ⊎ Pointed.SecondarySheet9

toCornerIndexed729 : Nested.NestedPointed729 → CornerIndexed729
toCornerIndexed729 (inj₁ (index , surface)) =
  inj₁ (Corners.fin8ToCorner index , surface)
toCornerIndexed729 (inj₂ secondary) = inj₂ secondary

fromCornerIndexed729 : CornerIndexed729 → Nested.NestedPointed729
fromCornerIndexed729 (inj₁ (corner , surface)) =
  inj₁ (Corners.cornerToFin8 corner , surface)
fromCornerIndexed729 (inj₂ secondary) = inj₂ secondary

fromAfterToCornerIndexed729 :
  (state : Nested.NestedPointed729) →
  fromCornerIndexed729 (toCornerIndexed729 state) ≡ state
fromAfterToCornerIndexed729 (inj₁ (index , surface))
  rewrite Corners.cornerAfterFin8 index = refl
fromAfterToCornerIndexed729 (inj₂ secondary) = refl

toAfterFromCornerIndexed729 :
  (state : CornerIndexed729) →
  toCornerIndexed729 (fromCornerIndexed729 state) ≡ state
toAfterFromCornerIndexed729 (inj₁ (corner , surface))
  rewrite Corners.fin8AfterCorner corner = refl
toAfterFromCornerIndexed729 (inj₂ secondary) = refl

------------------------------------------------------------------------
-- Direct chart from the original pointed carrier.
------------------------------------------------------------------------

pointedToCornerIndexed729 : Pointed.PointedAppraisal729 → CornerIndexed729
pointedToCornerIndexed729 =
  toCornerIndexed729 ∘ Nested.toNestedPointed729
  where
  _∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → A → C
  (f ∘ g) x = f (g x)

cornerIndexed729ToPointed : CornerIndexed729 → Pointed.PointedAppraisal729
cornerIndexed729ToPointed =
  Nested.fromNestedPointed729 ∘ fromCornerIndexed729
  where
  _∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → A → C
  (f ∘ g) x = f (g x)

pointedCornerRoundTrip :
  (state : Pointed.PointedAppraisal729) →
  cornerIndexed729ToPointed (pointedToCornerIndexed729 state) ≡ state
pointedCornerRoundTrip (inj₁ (Pointed.noncentralFineAddress index fine secondary))
  rewrite Corners.cornerAfterFin8 index = refl
pointedCornerRoundTrip (inj₂ (Pointed.centralSharedAddress secondary)) = refl

cornerPointedRoundTrip :
  (state : CornerIndexed729) →
  pointedToCornerIndexed729 (cornerIndexed729ToPointed state) ≡ state
cornerPointedRoundTrip (inj₁ (corner , (fine , secondary)))
  rewrite Corners.fin8AfterCorner corner = refl
cornerPointedRoundTrip (inj₂ secondary) = refl

------------------------------------------------------------------------
-- Exact power-aware arithmetic shadow.
------------------------------------------------------------------------

tenTimesThreeSquared : Nat
tenTimesThreeSquared = 10 * (3 * 3)

tenTimesThreeSquaredIsNinety : tenTimesThreeSquared ≡ 90
tenTimesThreeSquaredIsNinety = refl

cornerFibreDimension : Nat
cornerFibreDimension = 8 * tenTimesThreeSquared + (3 * 3)

cornerFibreDimensionIs729 : cornerFibreDimension ≡ 729
cornerFibreDimensionIs729 = refl

cornerRecursiveZetaDimension : Nat
cornerRecursiveZetaDimension = cornerFibreDimension * tenTimesThreeSquared

cornerRecursiveZetaDimensionIs65610 :
  cornerRecursiveZetaDimension ≡ 65610
cornerRecursiveZetaDimensionIs65610 = refl

cornerRecursiveThreePhaseBulk : Nat
cornerRecursiveThreePhaseBulk = 3 * cornerRecursiveZetaDimension

cornerRecursiveThreePhaseBulkIs196830 :
  cornerRecursiveThreePhaseBulk ≡ 196830
cornerRecursiveThreePhaseBulkIs196830 = refl

------------------------------------------------------------------------
-- Action-level promotion target.
------------------------------------------------------------------------

record CornerIndexedActionRecognition (Actor : Set) : Set₁ where
  field
    nestedAct : Actor → Nested.NestedPointed729 → Nested.NestedPointed729
    cornerAct : Actor → CornerIndexed729 → CornerIndexed729
    cornerChartIntertwines :
      (actor : Actor) →
      (state : Nested.NestedPointed729) →
      toCornerIndexed729 (nestedAct actor state)
      ≡ cornerAct actor (toCornerIndexed729 state)
open CornerIndexedActionRecognition public

record Pointed729CornerBoundary : Set where
  constructor pointed729CornerBoundary
  field
    anonymousFin8ReplacedByLiteralCornerCarrier : Bool
    cornerChartIsTwoSided : Bool
    exactShapeIsEightCornersTimesTenTimesThreeSquaredPlusThreeSquared : Bool
    recursive65610Generated : Bool
    recursive196830Generated : Bool
    cornerGeometryAloneIdentifiesMonsterAction : Bool
    sameActionIntertwinerStillRequired : Bool

canonicalPointed729CornerBoundary : Pointed729CornerBoundary
canonicalPointed729CornerBoundary =
  pointed729CornerBoundary true true true true true false true
