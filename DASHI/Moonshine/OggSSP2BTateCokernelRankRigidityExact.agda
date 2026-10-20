module DASHI.Moonshine.OggSSP2BTateCokernelRankRigidityExact where

------------------------------------------------------------------------
-- RANK RIGIDITY OF THE WEIGHT-TWO TATE NORM COKERNEL
--
-- Source-native dimensions:
--   M_minus = 98304,
--   target  = C_98280 + S_300.
--
-- Once the centralizer decomposition-matrix screen pays support separation,
-- the projection of the injective norm map into S_300 can use at most the
-- residual natural-24 composition lane.  Its kernel maps injectively into the
-- common C_98280 target.  Rank-nullity therefore has no slack:
--
--   rank residual projection = 24,
--   kernel dimension          = 98280.
--
-- Agda records the exact arithmetic closure and the runtime/source interfaces.
-- Lean owns the generic inequality compiler proving the squeeze from the two
-- one-sided bounds.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

minusDimension : Nat
minusDimension = 98304

commonTargetDimension : Nat
commonTargetDimension = 98280

residualNaturalDimension : Nat
residualNaturalDimension = 24

rankRigidityClosure :
  commonTargetDimension + residualNaturalDimension ≡ minusDimension
rankRigidityClosure = refl

forcedResidualRank : Nat
forcedResidualRank = 24

forcedCommonKernelDimension : Nat
forcedCommonKernelDimension = 98280

forcedRankNullityClosure :
  forcedCommonKernelDimension + forcedResidualRank ≡ minusDimension
forcedRankNullityClosure = refl

record RankRigidityBoundary : Set where
  constructor rank-rigidity-boundary
  field
    normMapInjectivitySourceNative : Bool
    supportSeparationScreenImplemented : Bool
    supportSeparationRuntimePaid : Bool
    residualRankUpperBoundPaid : Bool
    kernelCommonTargetUpperBoundPaid : Bool
    rankRigidityArithmeticPaid : Bool
    residualRankTwentyFourPaid : Bool
    commonKernelDimension98280Paid : Bool
    residualMapForcedFrobenius : Bool
    actualTateExteriorSquareWeldPaid : Bool

canonicalRankRigidityBoundary : RankRigidityBoundary
canonicalRankRigidityBoundary =
  rank-rigidity-boundary
    true true false false true true false false false false

supportSeparationRuntimeStillOpen :
  RankRigidityBoundary.supportSeparationRuntimePaid canonicalRankRigidityBoundary
  ≡ false
supportSeparationRuntimeStillOpen = refl

actualTateExteriorSquareWeldStillOpen :
  RankRigidityBoundary.actualTateExteriorSquareWeldPaid canonicalRankRigidityBoundary
  ≡ false
actualTateExteriorSquareWeldStillOpen = refl
