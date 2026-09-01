module DASHI.Moonshine.Base369PeriodicTernaryTorusPathRestrictionBidiExact where

------------------------------------------------------------------------
-- PERIODIC C3^9 TORUS -> NON-PERIODIC P3^9 STRATIFIED BOX
--
-- The same nine-trit carrier admits two different edge structures:
--
--   periodic:    C3^9, with wraparound +1 <-> -1
--   observational: P3^9, with -1 <-> 0 <-> +1 only
--
-- Every observational edge is a torus edge, but not conversely.  This makes
-- the earlier Heisenberg wraparound obstruction into an exact restriction
-- theorem rather than a dead-end mismatch.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as Heisenberg
import DASHI.Moonshine.Base369HeisenbergTranslationGridObstructionExact as Translation

------------------------------------------------------------------------
-- 1. Periodic one-axis C3 adjacency.
------------------------------------------------------------------------

data CyclicTritStep : SSP.SSPTrit → SSP.SSPTrit → Set where
  negToZero : CyclicTritStep SSP.sspNegOne SSP.sspZero
  zeroToNeg : CyclicTritStep SSP.sspZero SSP.sspNegOne
  zeroToPos : CyclicTritStep SSP.sspZero SSP.sspPosOne
  posToZero : CyclicTritStep SSP.sspPosOne SSP.sspZero
  posToNegWrap : CyclicTritStep SSP.sspPosOne SSP.sspNegOne
  negToPosWrap : CyclicTritStep SSP.sspNegOne SSP.sspPosOne

pathStepToCyclic :
  ∀ {a b} → Geometry.TritGridStep a b → CyclicTritStep a b
pathStepToCyclic Geometry.negToZero = negToZero
pathStepToCyclic Geometry.zeroToNeg = zeroToNeg
pathStepToCyclic Geometry.zeroToPos = zeroToPos
pathStepToCyclic Geometry.posToZero = posToZero

cyclicWrapPositiveToNegative :
  CyclicTritStep SSP.sspPosOne SSP.sspNegOne
cyclicWrapPositiveToNegative = posToNegWrap

cyclicWrapIsNotPathStep :
  Geometry.TritGridStep SSP.sspPosOne SSP.sspNegOne → ⊥
cyclicWrapIsNotPathStep = Geometry.noDirectPosToNeg

------------------------------------------------------------------------
-- 2. One 27-point periodic voxel.
------------------------------------------------------------------------

data TorusVoxelAdjacent : Geometry.Ternary27Point → Geometry.Ternary27Point → Set where
  torusAdjacentX : ∀ {x0 x1 y z} → CyclicTritStep x0 x1 →
    TorusVoxelAdjacent
      (Geometry.ternary27Point x0 y z)
      (Geometry.ternary27Point x1 y z)
  torusAdjacentY : ∀ {x y0 y1 z} → CyclicTritStep y0 y1 →
    TorusVoxelAdjacent
      (Geometry.ternary27Point x y0 z)
      (Geometry.ternary27Point x y1 z)
  torusAdjacentZ : ∀ {x y z0 z1} → CyclicTritStep z0 z1 →
    TorusVoxelAdjacent
      (Geometry.ternary27Point x y z0)
      (Geometry.ternary27Point x y z1)

pathVoxelEdgeEmbedsInTorus :
  ∀ {p q} → Geometry.HypervoxelAdjacent p q → TorusVoxelAdjacent p q
pathVoxelEdgeEmbedsInTorus (Geometry.adjacentX step) =
  torusAdjacentX (pathStepToCyclic step)
pathVoxelEdgeEmbedsInTorus (Geometry.adjacentY step) =
  torusAdjacentY (pathStepToCyclic step)
pathVoxelEdgeEmbedsInTorus (Geometry.adjacentZ step) =
  torusAdjacentZ (pathStepToCyclic step)

positiveToNegativeTorusEdge :
  TorusVoxelAdjacent
    Translation.translatedZeroAxisPoint
    Translation.translatedPositiveAxisPoint
positiveToNegativeTorusEdge = torusAdjacentX posToNegWrap

positiveToNegativeNotPathEdge :
  Geometry.HypervoxelAdjacent
    Translation.translatedZeroAxisPoint
    Translation.translatedPositiveAxisPoint → ⊥
positiveToNegativeNotPathEdge = Translation.translatedNativeEdgeWouldRequireWraparound

------------------------------------------------------------------------
-- 3. Full nine-coordinate torus adjacency on the same hyperfabric carrier.
------------------------------------------------------------------------

data TorusHyperformalAdjacent :
  Geometry.TernaryHyperformalPoint → Geometry.TernaryHyperformalPoint → Set where
  torusInteractionAdjacent : ∀ {i0 i1 a b} → TorusVoxelAdjacent i0 i1 →
    TorusHyperformalAdjacent
      (Geometry.ternaryHyperformalPoint i0 a b)
      (Geometry.ternaryHyperformalPoint i1 a b)
  torusAppraisalAAdjacent : ∀ {i a0 a1 b} → TorusVoxelAdjacent a0 a1 →
    TorusHyperformalAdjacent
      (Geometry.ternaryHyperformalPoint i a0 b)
      (Geometry.ternaryHyperformalPoint i a1 b)
  torusAppraisalBAdjacent : ∀ {i a b0 b1} → TorusVoxelAdjacent b0 b1 →
    TorusHyperformalAdjacent
      (Geometry.ternaryHyperformalPoint i a b0)
      (Geometry.ternaryHyperformalPoint i a b1)

pathFabricEdgeEmbedsInTorus :
  ∀ {p q} → Geometry.HyperformalAdjacent p q → TorusHyperformalAdjacent p q
pathFabricEdgeEmbedsInTorus (Geometry.interactionAdjacent edge) =
  torusInteractionAdjacent (pathVoxelEdgeEmbedsInTorus edge)
pathFabricEdgeEmbedsInTorus (Geometry.appraisalAAdjacent edge) =
  torusAppraisalAAdjacent (pathVoxelEdgeEmbedsInTorus edge)
pathFabricEdgeEmbedsInTorus (Geometry.appraisalBAdjacent edge) =
  torusAppraisalBAdjacent (pathVoxelEdgeEmbedsInTorus edge)

------------------------------------------------------------------------
-- 4. The earlier Heisenberg wrap is a legitimate periodic edge upstairs.
------------------------------------------------------------------------

heisenbergWrapLivesOnPeriodicTorus :
  TorusVoxelAdjacent
    Translation.translatedZeroAxisPoint
    Translation.translatedPositiveAxisPoint
heisenbergWrapLivesOnPeriodicTorus = positiveToNegativeTorusEdge

heisenbergWrapIsCutByPathRestriction :
  Geometry.HypervoxelAdjacent
    Translation.translatedZeroAxisPoint
    Translation.translatedPositiveAxisPoint → ⊥
heisenbergWrapIsCutByPathRestriction = positiveToNegativeNotPathEdge

------------------------------------------------------------------------
-- 5. BIDI boundary.
------------------------------------------------------------------------

record PeriodicPathRestrictionBoundary : Set where
  constructor periodicPathRestrictionBoundary
  field
    sameNineTritCarrier : Bool
    everyPathEdgeIsPeriodicEdge : Bool
    everyPeriodicEdgeIsPathEdge : Bool
    wraparoundExistsUpstairs : Bool
    wraparoundSurvivesPathRestriction : Bool
    heisenbergCyclicTranslationHasNaturalPeriodicHost : Bool
    periodicHostAlreadyEstablishesMonsterRepresentation : Bool

canonicalPeriodicPathRestrictionBoundary : PeriodicPathRestrictionBoundary
canonicalPeriodicPathRestrictionBoundary =
  periodicPathRestrictionBoundary
    true true false true false true false
