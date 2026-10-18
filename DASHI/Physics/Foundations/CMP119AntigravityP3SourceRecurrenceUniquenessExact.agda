{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityP3SourceRecurrenceUniquenessExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (subst)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Physics.Foundations.CMP119AntigravityBishopMatchedRecursionResidualExact as Cancel
import DASHI.Physics.Foundations.CMP119AntigravityP3StateForcesSourceIncrementExact as State
import DASHI.Physics.Foundations.CMP119AntigravitySourceHistoryBishopUVViewExact as UV
import DASHI.Physics.YangMills.BalabanClayP3PhysicalOneStepTransferExact as P3
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- SOURCE-FIRST RECURRENCE UNIQUENESS FOR THE P3 UV HISTORY
--
-- CMP109 and P3 both run UV-ward as
--
--   state k = state (suc k) + increment (suc k).
--
-- Therefore one common UV anchor plus one common increment at every edge
-- determines the whole state history.  This is the Bishop-setoid analogue of
-- the repo's existing OPE recurrence-uniqueness compiler.
------------------------------------------------------------------------

equalityAsBishopSetoid :
  ∀ {left right : Bishop.ℝ} →
  left ≡ right → Bishop._≃_ left right
equalityAsBishopSetoid {left} equality =
  subst (λ selected → Bishop._≃_ left selected) equality BishopP.≃-refl

bishopAddRightCancel :
  ∀ {left right common : Bishop.ℝ} →
  Bishop._≃_
    (Bishop._+_ left common)
    (Bishop._+_ right common) →
  Bishop._≃_ left right
bishopAddRightCancel {left} {right} {common} equality =
  Cancel.bishopAddLeftCancel
    (BishopP.≃-trans
      (BishopP.+-comm left common)
      (BishopP.≃-trans
        equality
        (BishopP.≃-symm (BishopP.+-comm right common))))

record P3SourceRecurrenceSameObject
    (trajectory : Flow.SourceNormalizedCouplingTrajectory)
    (recursion : P3.RunningCouplingRecursion Nat Bishop.ℝ) : Set₁ where
  field
    addIsBishopAdd :
      ∀ left right →
      Bishop._≃_
        (P3.add recursion left right)
        (Bishop._+_ left right)

    nextScaleIsUVPredecessor :
      ∀ depth →
      P3.nextScale recursion depth ≡ UV.uvNext depth

    sameUVAnchor :
      Bishop._≃_
        (P3.inverseCouplingSq recursion zero)
        (UV.uvInverseCoupling trajectory zero)

    totalIncrementSame :
      ∀ depth →
      Bishop._≃_
        (Bishop._+_
          (P3.betaLogBlocking recursion depth)
          (P3.remainder recursion depth))
        (UV.uvIncrement trajectory depth)

open P3SourceRecurrenceSameObject public

p3RecursionAtSuccessor :
  ∀ {trajectory recursion}
    (sameObject : P3SourceRecurrenceSameObject trajectory recursion)
    depth →
  Bishop._≃_
    (P3.inverseCouplingSq recursion depth)
    (Bishop._+_
      (P3.inverseCouplingSq recursion (suc depth))
      (Bishop._+_
        (P3.betaLogBlocking recursion (suc depth))
        (P3.remainder recursion (suc depth))))
p3RecursionAtSuccessor {recursion = recursion} sameObject depth =
  let
    raw :
      Bishop._≃_
        (P3.inverseCouplingSq recursion
          (P3.nextScale recursion (suc depth)))
        (P3.add recursion
          (P3.inverseCouplingSq recursion (suc depth))
          (P3.add recursion
            (P3.betaLogBlocking recursion (suc depth))
            (P3.remainder recursion (suc depth))))
    raw = equalityAsBishopSetoid (P3.recursionExact recursion (suc depth))

    shifted :
      Bishop._≃_
        (P3.inverseCouplingSq recursion depth)
        (P3.add recursion
          (P3.inverseCouplingSq recursion (suc depth))
          (P3.add recursion
            (P3.betaLogBlocking recursion (suc depth))
            (P3.remainder recursion (suc depth))))
    shifted =
      subst
        (λ selected →
          Bishop._≃_
            (P3.inverseCouplingSq recursion selected)
            (P3.add recursion
              (P3.inverseCouplingSq recursion (suc depth))
              (P3.add recursion
                (P3.betaLogBlocking recursion (suc depth))
                (P3.remainder recursion (suc depth))))
        )
        (nextScaleIsUVPredecessor sameObject (suc depth))
        raw
  in
  BishopP.≃-trans
    shifted
    (BishopP.≃-trans
      (addIsBishopAdd sameObject
        (P3.inverseCouplingSq recursion (suc depth))
        (P3.add recursion
          (P3.betaLogBlocking recursion (suc depth))
          (P3.remainder recursion (suc depth))))
      (BishopP.+-cong
        BishopP.≃-refl
        (addIsBishopAdd sameObject
          (P3.betaLogBlocking recursion (suc depth))
          (P3.remainder recursion (suc depth)))))

stateSameAtEveryDepth :
  ∀ {trajectory recursion} →
  P3SourceRecurrenceSameObject trajectory recursion →
  ∀ depth →
  Bishop._≃_
    (P3.inverseCouplingSq recursion depth)
    (UV.uvInverseCoupling trajectory depth)
stateSameAtEveryDepth sameObject zero = sameUVAnchor sameObject
stateSameAtEveryDepth {trajectory} {recursion} sameObject (suc depth) =
  let
    p3Step = p3RecursionAtSuccessor sameObject depth
    sourceStep = UV.uvRecurrenceSetoid trajectory (suc depth)

    p3ToSourceAtParent :
      Bishop._≃_
        (Bishop._+_
          (P3.inverseCouplingSq recursion (suc depth))
          (Bishop._+_
            (P3.betaLogBlocking recursion (suc depth))
            (P3.remainder recursion (suc depth))))
        (Bishop._+_
          (UV.uvInverseCoupling trajectory (suc depth))
          (UV.uvIncrement trajectory (suc depth)))
    p3ToSourceAtParent =
      BishopP.≃-trans
        (BishopP.≃-symm p3Step)
        (BishopP.≃-trans
          (stateSameAtEveryDepth sameObject depth)
          sourceStep)

    sameIncrement = totalIncrementSame sameObject (suc depth)

    commonIncrement :
      Bishop._≃_
        (Bishop._+_
          (P3.inverseCouplingSq recursion (suc depth))
          (UV.uvIncrement trajectory (suc depth)))
        (Bishop._+_
          (UV.uvInverseCoupling trajectory (suc depth))
          (UV.uvIncrement trajectory (suc depth)))
    commonIncrement =
      BishopP.≃-trans
        (BishopP.+-cong BishopP.≃-refl
          (BishopP.≃-symm sameIncrement))
        p3ToSourceAtParent
  in
  bishopAddRightCancel commonIncrement

asP3StateRepresentsSourceUV :
  ∀ {trajectory recursion} →
  P3SourceRecurrenceSameObject trajectory recursion →
  State.P3StateRepresentsSourceUV trajectory recursion
asP3StateRepresentsSourceUV sameObject = record
  { State.P3StateRepresentsSourceUV.addIsBishopAdd = addIsBishopAdd sameObject
  ; State.P3StateRepresentsSourceUV.inverseCouplingSame =
      stateSameAtEveryDepth sameObject
  ; State.P3StateRepresentsSourceUV.nextScaleIsUVPredecessor =
      nextScaleIsUVPredecessor sameObject
  }

allDepthStateWitnessRequired : Agda.Builtin.Bool.Bool
allDepthStateWitnessRequired = Agda.Builtin.Bool.false

oneUVAnchorAndOneStepIncrementSuffice : Agda.Builtin.Bool.Bool
oneUVAnchorAndOneStepIncrementSuffice = Agda.Builtin.Bool.true

p3SourceRecurrenceUniquenessCompilerLevel : ProofLevel
p3SourceRecurrenceUniquenessCompilerLevel = machineChecked
