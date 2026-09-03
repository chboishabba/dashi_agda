module DASHI.Moonshine.Base369Pointed729CornerTritSquareBidiExact where

------------------------------------------------------------------------
-- FULL GEOMETRIC REFINEMENT OF THE POINTED 729 CARRIER
--
-- Combine the literal eight-corner chart with the semantic refinement
--
--   90 ~= Completed10 x T^2
--
-- and replace the final shared Fin 9 by the same literal T^2 carrier.  The
-- pointed 729 geometry becomes
--
--   (Corner(T^3) x Completed10 x T^2) + T^2.
--
-- Its arithmetic shadow is exactly
--
--   3^6 = 8 * (10 * 3^2) + 3^2.
--
-- No action semantics are inferred from this carrier equivalence alone.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Product using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

import DASHI.Foundations.Base369Ternary27CornerEightExact as Corners
import DASHI.Foundations.Base369NonaryTritSquareExact as Square
import DASHI.Moonshine.Base369Pointed729CornerCubeBidiExact as Corner729
import DASHI.Moonshine.Base369CompletedTenTritSquareMultiplicityBidiExact as Completed

CornerCompleted729 : Set
CornerCompleted729 =
  (Corners.Corner3 × Completed.CompletedTenTritSquare)
  ⊎ Square.TritSquare

toCornerCompleted729 : Corner729.CornerIndexed729 → CornerCompleted729
toCornerCompleted729 (inj₁ (corner , surface)) =
  inj₁ (corner , Completed.toCompletedTenTritSquare surface)
toCornerCompleted729 (inj₂ secondary) =
  inj₂ (Completed.fin9ToTritSquare secondary)

fromCornerCompleted729 : CornerCompleted729 → Corner729.CornerIndexed729
fromCornerCompleted729 (inj₁ (corner , surface)) =
  inj₁ (corner , Completed.fromCompletedTenTritSquare surface)
fromCornerCompleted729 (inj₂ square) =
  inj₂ (Completed.tritSquareToFin9 square)

fromAfterToCornerCompleted729 :
  (state : Corner729.CornerIndexed729) →
  fromCornerCompleted729 (toCornerCompleted729 state) ≡ state
fromAfterToCornerCompleted729 (inj₁ (corner , surface))
  rewrite Completed.fromAfterToCompleted surface = refl
fromAfterToCornerCompleted729 (inj₂ secondary)
  rewrite Completed.tritSquareAfterFin9 secondary = refl

toAfterFromCornerCompleted729 :
  (state : CornerCompleted729) →
  toCornerCompleted729 (fromCornerCompleted729 state) ≡ state
toAfterFromCornerCompleted729 (inj₁ (corner , surface))
  rewrite Completed.toAfterFromCompleted surface = refl
toAfterFromCornerCompleted729 (inj₂ square)
  rewrite Completed.fin9AfterTritSquare square = refl

------------------------------------------------------------------------
-- Exact power-aware dimension ledger.
------------------------------------------------------------------------

threeSquared : Nat
threeSquared = 3 * 3

threeSquaredIsNine : threeSquared ≡ 9
threeSquaredIsNine = refl

completedTenTimesThreeSquared : Nat
completedTenTimesThreeSquared = 10 * threeSquared

completedTenTimesThreeSquaredIsNinety :
  completedTenTimesThreeSquared ≡ 90
completedTenTimesThreeSquaredIsNinety = refl

cornerCompletedDimension : Nat
cornerCompletedDimension =
  8 * completedTenTimesThreeSquared + threeSquared

cornerCompletedDimensionIsThreePowerSix :
  cornerCompletedDimension ≡ 729
cornerCompletedDimensionIsThreePowerSix = refl

nestedRegularPhaseDimension : Nat
nestedRegularPhaseDimension =
  cornerCompletedDimension * completedTenTimesThreeSquared

nestedRegularPhaseDimensionIs65610 :
  nestedRegularPhaseDimension ≡ 65610
nestedRegularPhaseDimensionIs65610 = refl

nestedThreePhaseBulkDimension : Nat
nestedThreePhaseBulkDimension = 3 * nestedRegularPhaseDimension

nestedThreePhaseBulkDimensionIs196830 :
  nestedThreePhaseBulkDimension ≡ 196830
nestedThreePhaseBulkDimensionIs196830 = refl

record CornerCompletedBoundary : Set where
  constructor cornerCompletedBoundary
  field
    eightIsLiteralCubeCorners : Bool
    ninetyIsCompletedTenTimesLiteralTritSquare : Bool
    centralNineIsSameLiteralTritSquareCarrier : Bool
    pointed729CarrierEquivalenceIsTwoSided : Bool
    threePowerSixRefactorGenerated : Bool
    regular65610RefactorGenerated : Bool
    threePhase196830RefactorGenerated : Bool
    carrierShapeAloneIdentifiesMonsterAction : Bool

canonicalCornerCompletedBoundary : CornerCompletedBoundary
canonicalCornerCompletedBoundary =
  cornerCompletedBoundary true true true true true true true false
