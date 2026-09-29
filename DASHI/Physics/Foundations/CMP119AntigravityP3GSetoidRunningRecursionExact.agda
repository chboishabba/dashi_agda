{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityP3GSetoidRunningRecursionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (subst)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Physics.Foundations.CMP119AntigravityBishopMatchedRecursionResidualExact as Cancel
import DASHI.Physics.Foundations.CMP119AntigravityP3GSetoidPhysicalCoreExact as Core
import DASHI.Physics.Foundations.CMP119AntigravitySourceHistoryBishopUVViewExact as UV
import DASHI.Physics.Foundations.CMP119AntigravityCMP109TrajectoryPlaquetteConstructorExact as Constructor
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow

------------------------------------------------------------------------
-- Setoid-level physical running coupling.  The legacy P3 version requires
-- intensional equality on Bishop reals, stronger than physical equality.
-- A quantitative remainder majorant is intentionally NOT postulated here.
------------------------------------------------------------------------

record SetoidRunningCouplingRecursion (Scale : Set) : Set₁ where
  field
    inverseCouplingSq : Scale → Bishop.ℝ
    betaLogBlocking : Scale → Bishop.ℝ
    remainder : Scale → Bishop.ℝ
    nextScale : Scale → Scale

    recursionExactSetoid : ∀ scale →
      Bishop._≃_
        (inverseCouplingSq (nextScale scale))
        (Bishop._+_
          (inverseCouplingSq scale)
          (Bishop._+_
            (betaLogBlocking scale)
            (remainder scale)))

open SetoidRunningCouplingRecursion public

fromPhysicalCore :
  ∀ {trajectory weld rich} →
  Core.P3GSetoidPhysicalGeometry
    {trajectory = trajectory} weld rich →
  SetoidRunningCouplingRecursion Nat
fromPhysicalCore {trajectory = trajectory} geometry = record
  { inverseCouplingSq = Core.physicalState trajectory
  ; betaLogBlocking = Core.physicalBetaLog geometry
  ; remainder = Core.physicalRemainder geometry
  ; nextScale = UV.uvNext
  ; recursionExactSetoid = Core.physicalRecurrenceSetoid geometry
  }

------------------------------------------------------------------------
-- Generic, *extensional* UV recurrence uniqueness.  This does not use the
-- legacy P3 recursionExact field, and only invokes Bishop setoid cancellation.
------------------------------------------------------------------------

record SameSourceUVIncrement
    (trajectory : Flow.SourceNormalizedCouplingTrajectory)
    (running : SetoidRunningCouplingRecursion Nat) : Set₁ where
  field
    predecessorScale : ∀ depth →
      nextScale running depth ≡ UV.uvNext depth

    initialState :
      Bishop._≃_
        (inverseCouplingSq running zero)
        (UV.uvInverseCoupling trajectory zero)

    increments :
      ∀ depth →
      Bishop._≃_
        (Bishop._+_
          (betaLogBlocking running depth)
          (remainder running depth))
        (UV.uvIncrement trajectory depth)

open SameSourceUVIncrement public

runningAtSuccessor :
  ∀ {trajectory running}
    (same : SameSourceUVIncrement trajectory running)
    depth →
  Bishop._≃_
    (inverseCouplingSq running depth)
    (Bishop._+_
      (inverseCouplingSq running (suc depth))
      (Bishop._+_
        (betaLogBlocking running (suc depth))
        (remainder running (suc depth))))
runningAtSuccessor {running = running} same depth =
  subst
    (λ selected →
      Bishop._≃_
        (inverseCouplingSq running selected)
        (Bishop._+_
          (inverseCouplingSq running (suc depth))
          (Bishop._+_
            (betaLogBlocking running (suc depth))
            (remainder running (suc depth)))))
    (predecessorScale same (suc depth))
    (recursionExactSetoid running (suc depth))

bishopAddRightCancel :
  ∀ {left right common : Bishop.ℝ} →
  Bishop._≃_
    (Bishop._+_ left common)
    (Bishop._+_ right common) →
  Bishop._≃_ left right
bishopAddRightCancel {left} {right} {common} proof =
  Cancel.bishopAddLeftCancel
    (BishopP.≃-trans
      (BishopP.+-comm left common)
      (BishopP.≃-trans
        proof
        (BishopP.≃-symm (BishopP.+-comm right common))))

stateSameAtEveryDepth :
  ∀ {trajectory running}
    (same : SameSourceUVIncrement trajectory running)
    depth →
  Bishop._≃_
    (inverseCouplingSq running depth)
    (UV.uvInverseCoupling trajectory depth)
stateSameAtEveryDepth same zero = initialState same
stateSameAtEveryDepth {trajectory} {running} same (suc depth) =
  let
    sourceStep = UV.uvRecurrenceSetoid trajectory (suc depth)
    currentStep = runningAtSuccessor same depth
    atParent :
      Bishop._≃_
        (Bishop._+_
          (inverseCouplingSq running (suc depth))
          (Bishop._+_
            (betaLogBlocking running (suc depth))
            (remainder running (suc depth))))
        (Bishop._+_
          (UV.uvInverseCoupling trajectory (suc depth))
          (UV.uvIncrement trajectory (suc depth)))
    atParent =
      BishopP.≃-trans
        (BishopP.≃-symm currentStep)
        (BishopP.≃-trans
          (stateSameAtEveryDepth same depth)
          sourceStep)

    withSameIncrement :
      Bishop._≃_
        (Bishop._+_
          (inverseCouplingSq running (suc depth))
          (UV.uvIncrement trajectory (suc depth)))
        (Bishop._+_
          (UV.uvInverseCoupling trajectory (suc depth))
          (UV.uvIncrement trajectory (suc depth)))
    withSameIncrement =
      BishopP.≃-trans
        (BishopP.+-cong BishopP.≃-refl
          (BishopP.≃-symm (increments same (suc depth))))
        atParent
  in
  bishopAddRightCancel withSameIncrement

physicalCoreSameSource :
  ∀ {trajectory weld rich}
    (geometry : Core.P3GSetoidPhysicalGeometry
      {trajectory = trajectory} weld rich) →
  SameSourceUVIncrement trajectory (fromPhysicalCore geometry)
physicalCoreSameSource {trajectory = trajectory} geometry = record
  { predecessorScale = λ depth → refl
  ; initialState = BishopP.≃-refl
  ; increments = λ { zero →
      Core.zeroTotalIncrementIsZero geometry
    ; (suc depth) →
      Core.positiveEdgeTotalIncrementSameSource geometry depth
    }
  }

physicalCoreHistoryUnique :
  ∀ {trajectory weld rich}
    (geometry : Core.P3GSetoidPhysicalGeometry
      {trajectory = trajectory} weld rich)
    depth →
  Bishop._≃_
    (inverseCouplingSq (fromPhysicalCore geometry) depth)
    (UV.uvInverseCoupling trajectory depth)
physicalCoreHistoryUnique geometry =
  stateSameAtEveryDepth (physicalCoreSameSource geometry)

------------------------------------------------------------------------
-- Remainder estimate is genuinely additional quantitative physics.  The
-- caller must provide an independently specified, non-tautological bound.
------------------------------------------------------------------------

record PhysicalRemainderMajorant
    (running : SetoidRunningCouplingRecursion Nat)
    (majorant : Nat → Bishop.ℝ) : Set₁ where
  field
    majorantNonnegative : ∀ depth →
      Bishop._≤_ Bishop.0ℝ (majorant depth)
    controlledUpper : ∀ depth →
      Bishop._≤_ (remainder running depth) (majorant depth)
    controlledLower : ∀ depth →
      Bishop._≤_
        (Bishop.-_ (majorant depth))
        (remainder running depth)

open PhysicalRemainderMajorant public
