module DASHI.Physics.YangMills.BalabanClayGate4DyadicRandomWalkTailExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4DyadicGeometricRootedSummabilityExact as Dyadic

------------------------------------------------------------------------
-- Explicit random-walk localization bound at dyadic contraction.
--
-- Tadeusz Bałaban,
-- "Regularity and Decay of Lattice Green's Functions",
-- Communications in Mathematical Physics 89 (1983), 571--597.
-- DOI: 10.1007/BF01214744.
--
-- If the norm of the depth-m random-walk shell is bounded by g 2^{-m},
-- induction bounds every finite localized correction by the corresponding
-- dyadic geometric partial sum.  The exact tail identity then gives 2g.
------------------------------------------------------------------------

record DyadicRandomWalkOrder : Set₁ where
  field
    LessEqual : ℚ → ℚ → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    addMonotone : ∀ {left leftUpper right rightUpper} →
      LessEqual left leftUpper → LessEqual right rightUpper →
      LessEqual (left + right) (leftUpper + rightUpper)

    tailNonnegative : ∀ amplitude depth →
      LessEqual 0ℚ (Dyadic.dyadicTail amplitude depth)

    leftBelowTotalFromNonnegativeTail : ∀ left tail total →
      left + tail ≡ total →
      LessEqual 0ℚ tail →
      LessEqual left total

open DyadicRandomWalkOrder public

asDyadicTailOrder : DyadicRandomWalkOrder → Dyadic.DyadicTailOrder
asDyadicTailOrder order = record
  { LessEqual = LessEqual order
  ; tailNonnegative = tailNonnegative order
  ; leftBelowTotalFromNonnegativeTail =
      leftBelowTotalFromNonnegativeTail order
  }

randomWalkPartialNorm : (Nat → ℚ) → Nat → ℚ
randomWalkPartialNorm shellNorm zero = 0ℚ
randomWalkPartialNorm shellNorm (suc depth) =
  shellNorm depth + randomWalkPartialNorm shellNorm depth

record DyadicRandomWalkShellBound
    (order : DyadicRandomWalkOrder) : Set₁ where
  field
    amplitude : ℚ
    shellNorm : Nat → ℚ

    shellBound : ∀ depth →
      LessEqual order
        (shellNorm depth)
        (amplitude * Dyadic.dyadicPower depth)

open DyadicRandomWalkShellBound public

randomWalkPartialBelowDyadicMajorant :
  ∀ {order : DyadicRandomWalkOrder}
    (bounds : DyadicRandomWalkShellBound order)
    depth →
  LessEqual order
    (randomWalkPartialNorm (shellNorm bounds) depth)
    (Dyadic.dyadicRootedPartial (amplitude bounds) depth)
randomWalkPartialBelowDyadicMajorant {order = order} bounds zero =
  reflexive order 0ℚ
randomWalkPartialBelowDyadicMajorant {order = order} bounds (suc depth) =
  addMonotone order
    (shellBound bounds depth)
    (randomWalkPartialBelowDyadicMajorant bounds depth)

randomWalkPartialBelowDoubleAmplitude :
  ∀ {order : DyadicRandomWalkOrder}
    (bounds : DyadicRandomWalkShellBound order)
    depth →
  LessEqual order
    (randomWalkPartialNorm (shellNorm bounds) depth)
    (amplitude bounds + amplitude bounds)
randomWalkPartialBelowDoubleAmplitude {order = order} bounds depth =
  transitive order
    (randomWalkPartialBelowDyadicMajorant bounds depth)
    (Dyadic.dyadicRootedPartialBelowDoubleAmplitude
      (asDyadicTailOrder order) (amplitude bounds) depth)

dyadicRandomWalkPartialMajorantLevel : ProofLevel
dyadicRandomWalkPartialMajorantLevel = machineChecked

dyadicRandomWalkDoubleAmplitudeLevel : ProofLevel
dyadicRandomWalkDoubleAmplitudeLevel = machineChecked

physicalRandomWalkDyadicShellInputsLevel : ProofLevel
physicalRandomWalkDyadicShellInputsLevel = conditional
