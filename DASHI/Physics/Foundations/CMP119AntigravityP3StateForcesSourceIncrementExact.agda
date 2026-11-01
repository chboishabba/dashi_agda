{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityP3StateForcesSourceIncrementExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Physics.Foundations.CMP119AntigravityBishopMatchedRecursionResidualExact as Cancel
import DASHI.Physics.Foundations.CMP119AntigravitySourceHistoryBishopUVViewExact as UV
import DASHI.Physics.YangMills.BalabanClayP3PhysicalOneStepTransferExact as P3
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- P3 STATE/STEP IDENTIFICATION ALREADY FORCES THE SOURCE INCREMENT
--
-- No independent `totalIncrementSame` field is mathematically needed once
-- P3's exact recursion is known to run on the same source UV state and the
-- same predecessor map.
------------------------------------------------------------------------

equalityAsBishopSetoid :
  ∀ {left right : Bishop.ℝ} →
  left ≡ right → Bishop._≃_ left right
equalityAsBishopSetoid {left} equality =
  subst (λ selected → Bishop._≃_ left selected) equality BishopP.≃-refl

record P3StateRepresentsSourceUV
    (trajectory : Flow.SourceNormalizedCouplingTrajectory)
    (recursion : P3.RunningCouplingRecursion Nat Bishop.ℝ) : Set₁ where
  field
    addIsBishopAdd :
      ∀ left right →
      Bishop._≃_
        (P3.add recursion left right)
        (Bishop._+_ left right)

    inverseCouplingSame :
      ∀ depth →
      Bishop._≃_
        (P3.inverseCouplingSq recursion depth)
        (UV.uvInverseCoupling trajectory depth)

    nextScaleIsUVPredecessor :
      ∀ depth →
      P3.nextScale recursion depth ≡ UV.uvNext depth

open P3StateRepresentsSourceUV public

p3RecursionInBishopNormalForm :
  ∀ {trajectory recursion} →
  P3StateRepresentsSourceUV trajectory recursion →
  ∀ depth →
  Bishop._≃_
    (UV.uvInverseCoupling trajectory (UV.uvNext depth))
    (Bishop._+_
      (UV.uvInverseCoupling trajectory depth)
      (Bishop._+_
        (P3.betaLogBlocking recursion depth)
        (P3.remainder recursion depth)))
p3RecursionInBishopNormalForm {trajectory} {recursion} state depth =
  let
    raw :
      Bishop._≃_
        (P3.inverseCouplingSq recursion (P3.nextScale recursion depth))
        (P3.add recursion
          (P3.inverseCouplingSq recursion depth)
          (P3.add recursion
            (P3.betaLogBlocking recursion depth)
            (P3.remainder recursion depth)))
    raw = equalityAsBishopSetoid (P3.recursionExact recursion depth)

    shiftedLeft :
      Bishop._≃_
        (P3.inverseCouplingSq recursion (UV.uvNext depth))
        (P3.add recursion
          (P3.inverseCouplingSq recursion depth)
          (P3.add recursion
            (P3.betaLogBlocking recursion depth)
            (P3.remainder recursion depth)))
    shiftedLeft =
      subst
        (λ selected →
          Bishop._≃_
            (P3.inverseCouplingSq recursion selected)
            (P3.add recursion
              (P3.inverseCouplingSq recursion depth)
              (P3.add recursion
                (P3.betaLogBlocking recursion depth)
                (P3.remainder recursion depth))))
        (nextScaleIsUVPredecessor state depth)
        raw

    normalizedRight :
      Bishop._≃_
        (P3.add recursion
          (P3.inverseCouplingSq recursion depth)
          (P3.add recursion
            (P3.betaLogBlocking recursion depth)
            (P3.remainder recursion depth)))
        (Bishop._+_
          (UV.uvInverseCoupling trajectory depth)
          (Bishop._+_
            (P3.betaLogBlocking recursion depth)
            (P3.remainder recursion depth)))
    normalizedRight =
      BishopP.≃-trans
        (addIsBishopAdd state
          (P3.inverseCouplingSq recursion depth)
          (P3.add recursion
            (P3.betaLogBlocking recursion depth)
            (P3.remainder recursion depth)))
        (BishopP.+-cong
          (inverseCouplingSame state depth)
          (addIsBishopAdd state
            (P3.betaLogBlocking recursion depth)
            (P3.remainder recursion depth)))
  in
  BishopP.≃-trans
    (BishopP.≃-symm
      (inverseCouplingSame state (UV.uvNext depth)))
    (BishopP.≃-trans shiftedLeft normalizedRight)

p3StateForcesTotalIncrement :
  ∀ {trajectory recursion} →
  P3StateRepresentsSourceUV trajectory recursion →
  ∀ depth →
  Bishop._≃_
    (Bishop._+_
      (P3.betaLogBlocking recursion depth)
      (P3.remainder recursion depth))
    (UV.uvIncrement trajectory depth)
p3StateForcesTotalIncrement {trajectory} {recursion} state depth =
  let
    sameOuter :
      Bishop._≃_
        (Bishop._+_
          (UV.uvInverseCoupling trajectory depth)
          (Bishop._+_
            (P3.betaLogBlocking recursion depth)
            (P3.remainder recursion depth)))
        (Bishop._+_
          (UV.uvInverseCoupling trajectory depth)
          (UV.uvIncrement trajectory depth))
    sameOuter =
      BishopP.≃-trans
        (BishopP.≃-symm (p3RecursionInBishopNormalForm state depth))
        (UV.uvRecurrenceSetoid trajectory depth)
  in
  Cancel.bishopAddLeftCancel sameOuter

asP3RepresentsSourceUVView :
  ∀ {trajectory recursion} →
  P3StateRepresentsSourceUV trajectory recursion →
  UV.P3RepresentsSourceUVView trajectory recursion
asP3RepresentsSourceUVView state = record
  { UV.P3RepresentsSourceUVView.addIsBishopAdd = addIsBishopAdd state
  ; UV.P3RepresentsSourceUVView.inverseCouplingSame = inverseCouplingSame state
  ; UV.P3RepresentsSourceUVView.nextScaleIsUVPredecessor =
      nextScaleIsUVPredecessor state
  ; UV.P3RepresentsSourceUVView.totalIncrementSame =
      p3StateForcesTotalIncrement state
  }

independentTotalIncrementWitnessRequired : Agda.Builtin.Bool.Bool
independentTotalIncrementWitnessRequired = Agda.Builtin.Bool.false

p3StateForcesSourceIncrementCompilerLevel : ProofLevel
p3StateForcesSourceIncrementCompilerLevel = machineChecked
