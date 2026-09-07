module DASHI.Moonshine.JInvariantRainbowFullTurnHyperformExact where

------------------------------------------------------------------------
-- RAINBOW / FULL-TURN / 369 / 27 HYPERFABRIC BRIDGE
--
-- INTROSPECTIVE STATUS
--
-- The observed rainbow is treated here as a continuous/full-turn phase object
-- viewed through finite equal-sector observers.  The sector observer does not
-- replace the continuous colour/wave payload carried elsewhere in the repo.
--
-- Exact finite content:
--   * a full turn is 360 degree-units,
--   * C3, C6, C9 and C27 are exact equal-sector partitions of that turn,
--   * C27 necessarily uses a rational degree width 40/3 rather than an integer
--     degree width,
--   * the existing C3 -> C9 -> C27 tower and 27-hypervoxel geometry remain
--     separate semantic carriers even though they share the same sector count.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)

import DASHI.Foundations.Base369TriadicPhaseTower as Tower
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Geometry.Base369SectorUnrollingFinite as Unroll

------------------------------------------------------------------------
-- 1. Exact rational degree partition of one full turn.
--
-- sectorWidthNumerator / sectorWidthDenominator is the width of one sector in
-- degrees.  We avoid division entirely and store the exact cross-multiplied
-- full-turn equation.
------------------------------------------------------------------------

fullTurnDegrees : Nat
fullTurnDegrees = 360

record FullTurnPartition : Set where
  constructor full-turn-partition
  field
    sectorCount : Nat
    sectorWidthNumerator : Nat
    sectorWidthDenominator : Nat
    coversFullTurnExactly :
      sectorCount * sectorWidthNumerator ≡
      fullTurnDegrees * sectorWidthDenominator

open FullTurnPartition public

partition3 : FullTurnPartition
partition3 = full-turn-partition 3 120 1 refl

partition6 : FullTurnPartition
partition6 = full-turn-partition 6 60 1 refl

partition9 : FullTurnPartition
partition9 = full-turn-partition 9 40 1 refl

partition27 : FullTurnPartition
partition27 = full-turn-partition 27 40 3 refl

partition3WidthIs120 : sectorWidthNumerator partition3 ≡ 120
partition3WidthIs120 = refl

partition6WidthIs60 : sectorWidthNumerator partition6 ≡ 60
partition6WidthIs60 = refl

partition9WidthIs40 : sectorWidthNumerator partition9 ≡ 40
partition9WidthIs40 = refl

partition27WidthIsFortyThirds :
  sectorWidthNumerator partition27 ≡ 40
  × sectorWidthDenominator partition27 ≡ 3
partition27WidthIsFortyThirds = refl , refl

------------------------------------------------------------------------
-- 2. Exact refinement arithmetic.
------------------------------------------------------------------------

sixIsBinaryRefinementOfThree : 6 ≡ 3 * 2
sixIsBinaryRefinementOfThree = refl

nineIsTernaryRefinementOfThree : 9 ≡ 3 * 3
nineIsTernaryRefinementOfThree = refl

twentySevenIsTernaryRefinementOfNine : 27 ≡ 9 * 3
twentySevenIsTernaryRefinementOfNine = refl

twentySevenIsThreeCubed : 27 ≡ 3 * 3 * 3
twentySevenIsThreeCubed = refl

------------------------------------------------------------------------
-- 3. Same count, distinct semantics.
--
-- Phase27 is the existing cyclic/refinement carrier.  Ternary27Point is the
-- existing 3 x 3 x 3 hypervoxel carrier.  They both have twenty-seven slots,
-- but no identification is asserted here.  A semantic bridge must be supplied
-- by a consumer that actually needs one.
------------------------------------------------------------------------

record Rainbow369HyperformCarrier : Set₁ where
  constructor rainbow-369-hyperform-carrier
  field
    level3 : Set
    level9 : Set
    level27Phase : Set
    level27Fabric : Set
    phaseTower : Tower.TriadicPhaseTowerFragmentReceipt
    fabricStateCount : Nat
    fabricStateCountIs27 : fabricStateCount ≡ 27

open Rainbow369HyperformCarrier public

canonicalRainbow369HyperformCarrier : Rainbow369HyperformCarrier
canonicalRainbow369HyperformCarrier =
  rainbow-369-hyperform-carrier
    (Tower.TriadicPhaseTowerFragmentReceipt.level3
      Tower.base369TriadicPhaseTowerFragmentReceipt)
    (Tower.TriadicPhaseTowerFragmentReceipt.level9
      Tower.base369TriadicPhaseTowerFragmentReceipt)
    Tower.Phase27
    Fabric.Ternary27Point
    Tower.base369TriadicPhaseTowerFragmentReceipt
    Fabric.hypervoxelStateCount
    Fabric.hypervoxelStateCountIs27

------------------------------------------------------------------------
-- 4. Unrolling compatibility.
--
-- The existing sector-unrolling owner proves exact finite linear ring profiles
-- for arbitrary discrete angle units.  This module uses that owner as the
-- finite geometry authority; it does not promote the real integral or a
-- physical colour model.
------------------------------------------------------------------------

threeSectorRingSample : Unroll.RingArcSample
threeSectorRingSample = Unroll.canonicalRingArcSample 120 1

nineSectorRingSample : Unroll.RingArcSample
nineSectorRingSample = Unroll.canonicalRingArcSample 40 1

------------------------------------------------------------------------
-- 5. Introspective / BIDI boundary.
------------------------------------------------------------------------

data RainbowAnalyticResidual : Set where
  missingContinuousColourPhaseCarrier : RainbowAnalyticResidual
  missingRationalSectorAnalyticEmbedding : RainbowAnalyticResidual
  missingWaveToThetaSameObjectBridge : RainbowAnalyticResidual
  missingThetaToJSameObjectBridge : RainbowAnalyticResidual
  missingMonsterActionIntertwiner : RainbowAnalyticResidual

firstRainbowAnalyticResidual : RainbowAnalyticResidual
firstRainbowAnalyticResidual = missingContinuousColourPhaseCarrier

record RainbowFullTurnBoundary : Set where
  constructor rainbow-full-turn-boundary
  field
    rainbowCanBeObservedByNEqualSectors : Bool
    threeSixNineTwentySevenShareFullTurnCarrier : Bool
    twentySevenHasIntegerDegreeSectorWidth : Bool
    sameTwentySevenCountImpliesSameSemanticCarrier : Bool
    finiteSectorPartitionIsPhysicalColourTheory : Bool
    finiteSectorPartitionIsThetaIdentity : Bool
    finiteSectorPartitionIsMonsterRepresentation : Bool

canonicalRainbowFullTurnBoundary : RainbowFullTurnBoundary
canonicalRainbowFullTurnBoundary =
  rainbow-full-turn-boundary
    true true false false false false false

------------------------------------------------------------------------
-- 6. BIDI consequence.
--
-- Forward search now owns the exact finite full-turn partition and the
-- C3/C9/C27 refinement carriers.  Backward search from theta/j/Monster still
-- requires a continuous complex phase/wave carrier on the same object.
------------------------------------------------------------------------

rainbowFiniteFrontier :
  FullTurnPartition × FullTurnPartition × FullTurnPartition × FullTurnPartition
rainbowFiniteFrontier = partition3 , (partition6 , (partition9 , partition27))
