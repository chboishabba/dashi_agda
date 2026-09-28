{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityP3LiteralPlaquetteRecurrenceSameObjectExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (0ℚ)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteCMP109UVSameObjectExact as LiteralToSource
import DASHI.Physics.Foundations.CMP119AntigravityP3LiteralPlaquetteCMP109SameObjectExact as Full
import DASHI.Physics.Foundations.CMP119AntigravityP3SourceRecurrenceUniquenessExact as Recurrence
import DASHI.Physics.Foundations.CMP119AntigravityBishopMatchedRecursionResidualExact as Cancel
import DASHI.Physics.Foundations.CMP119AntigravitySourceHistoryBishopUVViewExact as UV
import DASHI.Physics.YangMills.BalabanClayP3PhysicalOneStepTransferExact as P3
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4LiteralPlaquetteBetaEstimateExact as Literal
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- LOCAL P3/LITERAL SAME-OBJECT DATA SUFFICES
--
-- Do not pay the all-depth state equality directly.  Supply only:
--
--   * one UV anchor at depth zero;
--   * the source-faithful predecessor map;
--   * the literal total increment on every edge;
--   * Bishop addition.
--
-- The existing literal->CMP109 weld turns those local data into the source
-- recurrence package; recurrence uniqueness then reconstructs every P3 state.
------------------------------------------------------------------------

equalityAsBishopSetoid :
  ∀ {left right : Bishop.ℝ} →
  left ≡ right → Bishop._≃_ left right
equalityAsBishopSetoid {left} equality =
  subst (λ selected → Bishop._≃_ left selected) equality BishopP.≃-refl

record P3LiteralPlaquetteRecurrenceSameObject
    (dataSet : Plaquette.PhysicalRunningCouplingData Nat)
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

    sameUVAnchorAsLiteralNext :
      Bishop._≃_
        (P3.inverseCouplingSq recursion zero)
        (UV.embed (Plaquette.nextInverseCouplingSq dataSet zero))

    successorTotalIncrementSameLiteral :
      ∀ depth →
      Bishop._≃_
        (Bishop._+_
          (P3.betaLogBlocking recursion (suc depth))
          (P3.remainder recursion (suc depth)))
        (UV.embed (Literal.literalBetaStep dataSet depth))

open P3LiteralPlaquetteRecurrenceSameObject public

zeroTotalIncrementForced :
  ∀ {dataSet recursion} →
  P3LiteralPlaquetteRecurrenceSameObject dataSet recursion →
  Bishop._≃_
    (Bishop._+_
      (P3.betaLogBlocking recursion zero)
      (P3.remainder recursion zero))
    (UV.embed 0ℚ)
zeroTotalIncrementForced {recursion = recursion} local =
  let
    raw :
      Bishop._≃_
        (P3.inverseCouplingSq recursion (P3.nextScale recursion zero))
        (P3.add recursion
          (P3.inverseCouplingSq recursion zero)
          (P3.add recursion
            (P3.betaLogBlocking recursion zero)
            (P3.remainder recursion zero)))
    raw = equalityAsBishopSetoid (P3.recursionExact recursion zero)

    shifted :
      Bishop._≃_
        (P3.inverseCouplingSq recursion zero)
        (P3.add recursion
          (P3.inverseCouplingSq recursion zero)
          (P3.add recursion
            (P3.betaLogBlocking recursion zero)
            (P3.remainder recursion zero)))
    shifted =
      subst
        (λ selected →
          Bishop._≃_
            (P3.inverseCouplingSq recursion selected)
            (P3.add recursion
              (P3.inverseCouplingSq recursion zero)
              (P3.add recursion
                (P3.betaLogBlocking recursion zero)
                (P3.remainder recursion zero)))))
        (nextScaleIsUVPredecessor local zero)
        raw

    normalized :
      Bishop._≃_
        (P3.inverseCouplingSq recursion zero)
        (Bishop._+_
          (P3.inverseCouplingSq recursion zero)
          (Bishop._+_
            (P3.betaLogBlocking recursion zero)
            (P3.remainder recursion zero)))
    normalized =
      BishopP.≃-trans
        shifted
        (BishopP.≃-trans
          (addIsBishopAdd local
            (P3.inverseCouplingSq recursion zero)
            (P3.add recursion
              (P3.betaLogBlocking recursion zero)
              (P3.remainder recursion zero)))
          (BishopP.+-cong
            BishopP.≃-refl
            (addIsBishopAdd local
              (P3.betaLogBlocking recursion zero)
              (P3.remainder recursion zero))))

    withZero :
      Bishop._≃_
        (Bishop._+_ (P3.inverseCouplingSq recursion zero) Bishop.0ℝ)
        (Bishop._+_
          (P3.inverseCouplingSq recursion zero)
          (Bishop._+_
            (P3.betaLogBlocking recursion zero)
            (P3.remainder recursion zero)))
    withZero =
      BishopP.≃-trans
        (BishopP.+-identityʳ (P3.inverseCouplingSq recursion zero))
        normalized
  in
  BishopP.≃-trans
    (Cancel.bishopAddLeftCancel withZero)
    (BishopP.≃-symm
      (DASHI.Physics.Closure.NSTriadKNMurrayBishopDirectCanonicalCarrier.bishopEmbedZero))
asSourceRecurrenceSameObject :
  ∀ {dataSet trajectory recursion} →
  P3LiteralPlaquetteRecurrenceSameObject dataSet recursion →
  LiteralToSource.LiteralPlaquetteCMP109UVSameObject dataSet trajectory →
  Recurrence.P3SourceRecurrenceSameObject trajectory recursion
asSourceRecurrenceSameObject
    {dataSet = dataSet} {trajectory = trajectory} {recursion = recursion}
    local literalWeld = record
  { Recurrence.P3SourceRecurrenceSameObject.addIsBishopAdd =
      addIsBishopAdd local
  ; Recurrence.P3SourceRecurrenceSameObject.nextScaleIsUVPredecessor =
      nextScaleIsUVPredecessor local
  ; Recurrence.P3SourceRecurrenceSameObject.sameUVAnchor =
      BishopP.≃-trans
        (sameUVAnchorAsLiteralNext local)
        (equalityAsBishopSetoid
          (LiteralToSource.nextAtStepIsSourceCurrent literalWeld zero))
  ; Recurrence.P3SourceRecurrenceSameObject.totalIncrementSame =
      λ
        { zero → zeroTotalIncrementForced local
        ; (suc depth) →
            BishopP.≃-trans
              (successorTotalIncrementSameLiteral local depth)
              (subst
                (λ selected →
                  Bishop._≃_
                    (UV.embed (Literal.literalBetaStep dataSet depth))
                    (UV.embed selected))
                (LiteralToSource.literalBetaAtStepIsSourceSuccessorBeta
                  literalWeld depth)
                BishopP.≃-refl)
        }
  }

asFullLiteralPlaquetteUVView :
  ∀ {dataSet trajectory recursion} →
  P3LiteralPlaquetteRecurrenceSameObject dataSet recursion →
  LiteralToSource.LiteralPlaquetteCMP109UVSameObject dataSet trajectory →
  Full.P3RepresentsLiteralPlaquetteUVView dataSet recursion
asFullLiteralPlaquetteUVView
    {dataSet = dataSet} {trajectory = trajectory} {recursion = recursion}
    local literalWeld =
  let
    sourceRecurrence = asSourceRecurrenceSameObject local literalWeld
    sourceState = Recurrence.stateSameAtEveryDepth sourceRecurrence
  in
  record
    { Full.P3RepresentsLiteralPlaquetteUVView.addIsBishopAdd =
        addIsBishopAdd local
    ; Full.P3RepresentsLiteralPlaquetteUVView.inverseCouplingSameLiteral =
        λ depth →
          BishopP.≃-trans
            (sourceState depth)
            (BishopP.≃-symm
              (equalityAsBishopSetoid
                (LiteralToSource.nextAtStepIsSourceCurrent
                  literalWeld depth)))
    ; Full.P3RepresentsLiteralPlaquetteUVView.nextScaleIsUVPredecessor =
        nextScaleIsUVPredecessor local
    ; Full.P3RepresentsLiteralPlaquetteUVView.zeroTotalIncrementSame =
        zeroTotalIncrementForced local
    ; Full.P3RepresentsLiteralPlaquetteUVView.successorTotalIncrementSameLiteral =
        successorTotalIncrementSameLiteral local
    }

allDepthP3LiteralStateWitnessRequired : Agda.Builtin.Bool.Bool
allDepthP3LiteralStateWitnessRequired = Agda.Builtin.Bool.false

oneUVAnchorPlusLiteralIncrementsSuffice : Agda.Builtin.Bool.Bool
oneUVAnchorPlusLiteralIncrementsSuffice = Agda.Builtin.Bool.true

p3LiteralPlaquetteRecurrenceCompilerLevel : ProofLevel
p3LiteralPlaquetteRecurrenceCompilerLevel = machineChecked
