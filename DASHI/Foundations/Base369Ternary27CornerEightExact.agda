module DASHI.Foundations.Base369Ternary27CornerEightExact where

------------------------------------------------------------------------
-- LITERAL EIGHT CORNERS OF THE BASE369 TERNARY 27-CUBE
--
-- The existing stratification owner already proves that a 3x3x3 ternary cube
-- has exactly eight corners: points whose three coordinates are all outer
-- {-1,+1}.  This owner exposes those corners as the literal product
--
--   OuterSign^3 ~= Fin 8,
--
-- and maps each sign triple to the existing Ternary27Point carrier.  The
-- chart is geometric only; it does not identify these corners with any
-- Monster multiplicity or action without a further same-object receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin.Base using (Fin; zero; suc)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369Ternary27HypervoxelStratificationExact as Strata

data OuterSign : Set where
  negativeOuter positiveOuter : OuterSign

outerTrit : OuterSign → SSP.SSPTrit
outerTrit negativeOuter = SSP.sspNegOne
outerTrit positiveOuter = SSP.sspPosOne

record Corner3 : Set where
  constructor corner3
  field
    cornerX : OuterSign
    cornerY : OuterSign
    cornerZ : OuterSign
open Corner3 public

cornerPoint : Corner3 → Geometry.Ternary27Point
cornerPoint (corner3 x y z) =
  Geometry.ternary27Point (outerTrit x) (outerTrit y) (outerTrit z)

cornerPointIsCorner :
  (corner : Corner3) →
  Strata.voxelStratum (cornerPoint corner) ≡ Strata.cornerStratum
cornerPointIsCorner (corner3 negativeOuter negativeOuter negativeOuter) = refl
cornerPointIsCorner (corner3 negativeOuter negativeOuter positiveOuter) = refl
cornerPointIsCorner (corner3 negativeOuter positiveOuter negativeOuter) = refl
cornerPointIsCorner (corner3 negativeOuter positiveOuter positiveOuter) = refl
cornerPointIsCorner (corner3 positiveOuter negativeOuter negativeOuter) = refl
cornerPointIsCorner (corner3 positiveOuter negativeOuter positiveOuter) = refl
cornerPointIsCorner (corner3 positiveOuter positiveOuter negativeOuter) = refl
cornerPointIsCorner (corner3 positiveOuter positiveOuter positiveOuter) = refl

------------------------------------------------------------------------
-- Exact Fin 8 chart.  The bit ordering is x-major, then y, then z.
------------------------------------------------------------------------

fin8ToCorner : Fin 8 → Corner3
fin8ToCorner zero = corner3 negativeOuter negativeOuter negativeOuter
fin8ToCorner (suc zero) = corner3 negativeOuter negativeOuter positiveOuter
fin8ToCorner (suc (suc zero)) = corner3 negativeOuter positiveOuter negativeOuter
fin8ToCorner (suc (suc (suc zero))) = corner3 negativeOuter positiveOuter positiveOuter
fin8ToCorner (suc (suc (suc (suc zero)))) = corner3 positiveOuter negativeOuter negativeOuter
fin8ToCorner (suc (suc (suc (suc (suc zero))))) = corner3 positiveOuter negativeOuter positiveOuter
fin8ToCorner (suc (suc (suc (suc (suc (suc zero)))))) = corner3 positiveOuter positiveOuter negativeOuter
fin8ToCorner (suc (suc (suc (suc (suc (suc (suc zero))))))) = corner3 positiveOuter positiveOuter positiveOuter

cornerToFin8 : Corner3 → Fin 8
cornerToFin8 (corner3 negativeOuter negativeOuter negativeOuter) = zero
cornerToFin8 (corner3 negativeOuter negativeOuter positiveOuter) = suc zero
cornerToFin8 (corner3 negativeOuter positiveOuter negativeOuter) = suc (suc zero)
cornerToFin8 (corner3 negativeOuter positiveOuter positiveOuter) = suc (suc (suc zero))
cornerToFin8 (corner3 positiveOuter negativeOuter negativeOuter) = suc (suc (suc (suc zero)))
cornerToFin8 (corner3 positiveOuter negativeOuter positiveOuter) = suc (suc (suc (suc (suc zero))))
cornerToFin8 (corner3 positiveOuter positiveOuter negativeOuter) = suc (suc (suc (suc (suc (suc zero)))))
cornerToFin8 (corner3 positiveOuter positiveOuter positiveOuter) = suc (suc (suc (suc (suc (suc (suc zero))))))

cornerAfterFin8 : (index : Fin 8) → cornerToFin8 (fin8ToCorner index) ≡ index
cornerAfterFin8 zero = refl
cornerAfterFin8 (suc zero) = refl
cornerAfterFin8 (suc (suc zero)) = refl
cornerAfterFin8 (suc (suc (suc zero))) = refl
cornerAfterFin8 (suc (suc (suc (suc zero)))) = refl
cornerAfterFin8 (suc (suc (suc (suc (suc zero))))) = refl
cornerAfterFin8 (suc (suc (suc (suc (suc (suc zero)))))) = refl
cornerAfterFin8 (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl

fin8AfterCorner : (corner : Corner3) → fin8ToCorner (cornerToFin8 corner) ≡ corner
fin8AfterCorner (corner3 negativeOuter negativeOuter negativeOuter) = refl
fin8AfterCorner (corner3 negativeOuter negativeOuter positiveOuter) = refl
fin8AfterCorner (corner3 negativeOuter positiveOuter negativeOuter) = refl
fin8AfterCorner (corner3 negativeOuter positiveOuter positiveOuter) = refl
fin8AfterCorner (corner3 positiveOuter negativeOuter negativeOuter) = refl
fin8AfterCorner (corner3 positiveOuter negativeOuter positiveOuter) = refl
fin8AfterCorner (corner3 positiveOuter positiveOuter negativeOuter) = refl
fin8AfterCorner (corner3 positiveOuter positiveOuter positiveOuter) = refl

record CornerEightBoundary : Set where
  constructor cornerEightBoundary
  field
    cornerCarrierIsOuterSignCubed : Bool
    everyCornerMapsToExistingCornerStratum : Bool
    fin8ChartIsTwoSided : Bool
    eightIndicesGainGeometricCornerMeaning : Bool
    geometricCornerChartConstructsMonsterAction : Bool

canonicalCornerEightBoundary : CornerEightBoundary
canonicalCornerEightBoundary =
  cornerEightBoundary true true true true false
