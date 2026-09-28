{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityP3LiteralPlaquetteCMP109SameObjectExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (0ℚ)
open import Relation.Binary.PropositionalEquality using (subst)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Physics.Closure.NSTriadKNMurrayBishopDirectCanonicalCarrier as Carrier

import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteCMP109UVSameObjectExact as LiteralToSource
import DASHI.Physics.Foundations.CMP119AntigravitySourceHistoryBishopUVViewExact as UV
import DASHI.Physics.YangMills.BalabanClayP3PhysicalOneStepTransferExact as P3
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4LiteralPlaquetteBetaEstimateExact as Literal
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- P3/BISHOP -> LITERAL PLAQUETTE -> CMP109
--
-- The repository already owns the literal-plaquette -> CMP109 UV weld.
-- This module makes that object the unique intermediate target for the
-- remaining P3 same-object payment.
--
-- No new running-coupling arithmetic is introduced here.  The P3 recursion
-- only has to identify its Bishop-valued coordinates with the embedded
-- literal plaquette producer.  The existing literal weld then transports
-- those coordinates to the exact CMP109 source history.
------------------------------------------------------------------------

record P3RepresentsLiteralPlaquetteUVView
    (dataSet : Plaquette.PhysicalRunningCouplingData Nat)
    (recursion : P3.RunningCouplingRecursion Nat Bishop.ℝ) : Set₁ where
  field
    addIsBishopAdd :
      ∀ left right →
      Bishop._≃_
        (P3.add recursion left right)
        (Bishop._+_ left right)

    inverseCouplingSameLiteral :
      ∀ depth →
      Bishop._≃_
        (P3.inverseCouplingSq recursion depth)
        (UV.embed (Plaquette.nextInverseCouplingSq dataSet depth))

    nextScaleIsUVPredecessor :
      ∀ depth →
      P3.nextScale recursion depth ≡ UV.uvNext depth

    zeroTotalIncrementSame :
      Bishop._≃_
        (Bishop._+_
          (P3.betaLogBlocking recursion zero)
          (P3.remainder recursion zero))
        (UV.embed 0ℚ)

    successorTotalIncrementSameLiteral :
      ∀ depth →
      Bishop._≃_
        (Bishop._+_
          (P3.betaLogBlocking recursion (suc depth))
          (P3.remainder recursion (suc depth)))
        (UV.embed (Literal.literalBetaStep dataSet depth))

open P3RepresentsLiteralPlaquetteUVView public

p3LiteralPlaquetteThenCMP109 :
  ∀ {dataSet trajectory recursion} →
  P3RepresentsLiteralPlaquetteUVView dataSet recursion →
  LiteralToSource.LiteralPlaquetteCMP109UVSameObject dataSet trajectory →
  UV.P3RepresentsSourceUVView trajectory recursion
p3LiteralPlaquetteThenCMP109
    {dataSet = dataSet} {trajectory = trajectory} {recursion = recursion}
    p3 literalWeld = record
  { UV.P3RepresentsSourceUVView.addIsBishopAdd =
      addIsBishopAdd p3

  ; UV.P3RepresentsSourceUVView.inverseCouplingSame =
      λ depth →
        subst
          (λ selected →
            Bishop._≃_
              (P3.inverseCouplingSq recursion depth)
              (UV.embed selected))
          (LiteralToSource.nextAtStepIsSourceCurrent literalWeld depth)
          (inverseCouplingSameLiteral p3 depth)

  ; UV.P3RepresentsSourceUVView.nextScaleIsUVPredecessor =
      nextScaleIsUVPredecessor p3

  ; UV.P3RepresentsSourceUVView.totalIncrementSame =
      λ
        { zero →
            zeroTotalIncrementSame p3
        ; (suc depth) →
            subst
              (λ selected →
                Bishop._≃_
                  (Bishop._+_
                    (P3.betaLogBlocking recursion (suc depth))
                    (P3.remainder recursion (suc depth)))
                  (UV.embed selected))
              (LiteralToSource.literalBetaIsSourceBeta literalWeld depth)
              (successorTotalIncrementSameLiteral p3 depth)
        }
  }

------------------------------------------------------------------------
-- FRONTIER RECUT
--
-- After this compiler, the old direct P3 -> CMP109 same-object obligation is
-- redundant.  The only remaining P3 provenance task is to identify the P3
-- Bishop coordinates with the already-physical literal plaquette producer.
------------------------------------------------------------------------

directP3ToCMP109WeldRequired : Agda.Builtin.Bool.Bool
directP3ToCMP109WeldRequired = Agda.Builtin.Bool.false

p3ToLiteralPlaquetteWeldStillRequired : Agda.Builtin.Bool.Bool
p3ToLiteralPlaquetteWeldStillRequired = Agda.Builtin.Bool.true

p3LiteralPlaquetteCMP109CompilerLevel : ProofLevel
p3LiteralPlaquetteCMP109CompilerLevel = machineChecked

p3LiteralPlaquetteSameObjectLevel : ProofLevel
p3LiteralPlaquetteSameObjectLevel = conditional


------------------------------------------------------------------------
-- SPLIT-LEVEL P3 -> LITERAL PLAQUETTE COMPILER
--
-- The P3 producer naturally exposes the perturbative beta contribution and
-- the controlled remainder separately.  The literal plaquette producer does
-- too:
--
--   beta_Z   = vacuum-polarization plaquette coefficient
--   beta_int = localized interaction remainder.
--
-- Identifying those two coordinates separately is stronger than identifying
-- only their sum, and it is exactly the provenance needed by the running-
-- coupling convention constructor.
------------------------------------------------------------------------

record P3RepresentsLiteralPlaquetteSplitUVView
    (dataSet : Plaquette.PhysicalRunningCouplingData Nat)
    (recursion : P3.RunningCouplingRecursion Nat Bishop.ℝ) : Set₁ where
  field
    addIsBishopAdd :
      ∀ left right →
      Bishop._≃_
        (P3.add recursion left right)
        (Bishop._+_ left right)

    inverseCouplingSameLiteral :
      ∀ depth →
      Bishop._≃_
        (P3.inverseCouplingSq recursion depth)
        (UV.embed (Plaquette.nextInverseCouplingSq dataSet depth))

    nextScaleIsUVPredecessor :
      ∀ depth →
      P3.nextScale recursion depth ≡ UV.uvNext depth

    zeroTotalIncrementSame :
      Bishop._≃_
        (Bishop._+_
          (P3.betaLogBlocking recursion zero)
          (P3.remainder recursion zero))
        (UV.embed 0ℚ)

    betaLogBlockingSameLiteralGaussian :
      ∀ depth →
      Bishop._≃_
        (P3.betaLogBlocking recursion (suc depth))
        (UV.embed (Literal.literalBetaZ dataSet depth))

    remainderSameLiteralInteraction :
      ∀ depth →
      Bishop._≃_
        (P3.remainder recursion (suc depth))
        (UV.embed (Literal.literalBetaInt dataSet depth))

open P3RepresentsLiteralPlaquetteSplitUVView public

splitViewAsTotalView :
  ∀ {dataSet recursion} →
  P3RepresentsLiteralPlaquetteSplitUVView dataSet recursion →
  P3RepresentsLiteralPlaquetteUVView dataSet recursion
splitViewAsTotalView {dataSet = dataSet} {recursion = recursion} splitView = record
  { P3RepresentsLiteralPlaquetteUVView.addIsBishopAdd =
      P3RepresentsLiteralPlaquetteSplitUVView.addIsBishopAdd splitView

  ; P3RepresentsLiteralPlaquetteUVView.inverseCouplingSameLiteral =
      P3RepresentsLiteralPlaquetteSplitUVView.inverseCouplingSameLiteral splitView

  ; P3RepresentsLiteralPlaquetteUVView.nextScaleIsUVPredecessor =
      P3RepresentsLiteralPlaquetteSplitUVView.nextScaleIsUVPredecessor splitView

  ; P3RepresentsLiteralPlaquetteUVView.zeroTotalIncrementSame =
      P3RepresentsLiteralPlaquetteSplitUVView.zeroTotalIncrementSame splitView

  ; P3RepresentsLiteralPlaquetteUVView.successorTotalIncrementSameLiteral =
      λ depth →
        BishopP.≃-trans
          (BishopP.+-cong
            (betaLogBlockingSameLiteralGaussian splitView depth)
            (remainderSameLiteralInteraction splitView depth))
          (BishopP.≃-symm
            (Carrier.bishopEmbedAdd
              (Literal.literalBetaZ dataSet depth)
              (Literal.literalBetaInt dataSet depth)))
  }

p3LiteralPlaquetteSplitThenCMP109 :
  ∀ {dataSet trajectory recursion} →
  P3RepresentsLiteralPlaquetteSplitUVView dataSet recursion →
  LiteralToSource.LiteralPlaquetteCMP109UVSameObject dataSet trajectory →
  UV.P3RepresentsSourceUVView trajectory recursion
p3LiteralPlaquetteSplitThenCMP109 splitView literalWeld =
  p3LiteralPlaquetteThenCMP109
    (splitViewAsTotalView splitView)
    literalWeld

totalIncrementOnlyIdentificationRequiredOnPreferredRoute :
  Agda.Builtin.Bool.Bool
totalIncrementOnlyIdentificationRequiredOnPreferredRoute =
  Agda.Builtin.Bool.false

gaussianAndInteractionCoordinatesArePreferred :
  Agda.Builtin.Bool.Bool
gaussianAndInteractionCoordinatesArePreferred =
  Agda.Builtin.Bool.true
