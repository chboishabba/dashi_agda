module DASHI.Analysis.RiemannSSP15PartitionSeparationExact where

------------------------------------------------------------------------
-- THREE DISTINCT 15-WAY STRUCTURES
--
-- 1. RH/SSP15 indexing codec:
--
--      5 × 3 = 15
--
--    ComplementMode5 × RHDepthFiveRole, exactly reindexed as the existing
--    SSP15 internal mode × balanced-phase carrier.
--
-- 2. CM arithmetic partition over Q(sqrt(-7)):
--
--      5 + 9 + 1 = 15
--
--    split + inert + ramified SSP primes.
--
-- 3. Hecke / atom semantic grammar:
--
--      7 + 7 + 1 = 15.
--
-- These are distinct structures.  Equal totals do not supply a partition
-- isomorphism, semantic identity, or RH arithmetic interpretation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannSSP15DepthFiveRoleCodecExact as RHCodec
import DASHI.Physics.Closure.SSP15CMFieldSplittingCorrectionReceipt as CM
import DASHI.Physics.Closure.SSP7Plus7Plus1AtomGrammarReceipt as Atom
import DASHI.Physics.Closure.HeckeCarrierVsCMSplittingReceipt as Separation

------------------------------------------------------------------------
-- Exact totals.
------------------------------------------------------------------------

rhFiveTimesThreeIsFifteen :
  5 * RHCodec.rhDepthFiveRoleCount ≡ 15
rhFiveTimesThreeIsFifteen =
  RHCodec.fiveModesTimesThreeRolesIsFifteen

cmFivePlusNinePlusOneIsFifteen :
  CM.splitCount CM.canonicalSSP15CMFieldSplittingCorrectionReceipt
  + CM.inertCount CM.canonicalSSP15CMFieldSplittingCorrectionReceipt
  + CM.ramifiedCount CM.canonicalSSP15CMFieldSplittingCorrectionReceipt
  ≡ 15
cmFivePlusNinePlusOneIsFifteen = refl

heckeSevenPlusSevenPlusOneIsFifteen :
  Atom.mirrorAVariables Atom.canonicalSSP7Plus7Plus1AtomGrammarReceipt
  + Atom.mirrorBVariables Atom.canonicalSSP7Plus7Plus1AtomGrammarReceipt
  + Atom.spareSignVariable Atom.canonicalSSP7Plus7Plus1AtomGrammarReceipt
  ≡ 15
heckeSevenPlusSevenPlusOneIsFifteen = refl

------------------------------------------------------------------------
-- Existing authoritative separation: CM != Hecke atom grammar.
------------------------------------------------------------------------

cmAndHeckeAlreadyProvedDistinct :
  Separation.notSamePartitionFlag
    Separation.canonicalHeckeCarrierVsCMSplittingReceipt
  ≡ true
cmAndHeckeAlreadyProvedDistinct =
  Separation.canonicalHeckeCMNotSamePartition

------------------------------------------------------------------------
-- RH codec is a product decomposition, not either additive partition.
------------------------------------------------------------------------

data RHCodecIsCMSplittingPartition : Set where
data RHCodecIsHeckeAtomGrammar : Set where
data EqualFifteenTotalsCreateSamePartition : Set where

rhCodecNotPromotedToCMSplitting :
  RHCodecIsCMSplittingPartition -> ⊥
rhCodecNotPromotedToCMSplitting ()

rhCodecNotPromotedToHeckeAtomGrammar :
  RHCodecIsHeckeAtomGrammar -> ⊥
rhCodecNotPromotedToHeckeAtomGrammar ()

equalFifteenTotalsDoNotCreateSamePartition :
  EqualFifteenTotalsCreateSamePartition -> ⊥
equalFifteenTotalsDoNotCreateSamePartition ()

------------------------------------------------------------------------
-- Shape taxonomy.
------------------------------------------------------------------------

data FifteenShapeKind : Set where
  productFiveByThree :
    FifteenShapeKind
  additiveFiveNineOne :
    FifteenShapeKind
  additiveSevenSevenOne :
    FifteenShapeKind

rhCodecShape : FifteenShapeKind
rhCodecShape = productFiveByThree

cmShape : FifteenShapeKind
cmShape = additiveFiveNineOne

heckeShape : FifteenShapeKind
heckeShape = additiveSevenSevenOne

record RiemannSSP15PartitionSeparationBoundary : Set where
  constructor riemann-ssp15-partition-separation-boundary
  field
    rhFiveTimesThreeCountOwned : Bool
    cmFiveNineOneCountOwned : Bool
    heckeSevenSevenOneCountOwned : Bool
    existingCMHeckeSeparationReused : Bool
    rhCodecPromotedToCMPartition : Bool
    rhCodecPromotedToHeckeGrammar : Bool
    equalTotalPromotedToSamePartition : Bool

canonicalRiemannSSP15PartitionSeparationBoundary :
  RiemannSSP15PartitionSeparationBoundary
canonicalRiemannSSP15PartitionSeparationBoundary =
  riemann-ssp15-partition-separation-boundary
    true true true true
    false false false
