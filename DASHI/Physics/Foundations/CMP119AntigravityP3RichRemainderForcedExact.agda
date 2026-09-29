{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityP3RichRemainderForcedExact where

open import Agda.Builtin.Nat using (Nat; suc)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Physics.Closure.NSTriadKNMurrayBishopDirectCanonicalCarrier as Carrier
import DASHI.Physics.Foundations.CMP119AntigravityBishopMatchedRecursionResidualExact as Cancel
import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteCMP109UVSameObjectExact as LiteralToSource
import DASHI.Physics.Foundations.CMP119AntigravityP3StateForcesSourceIncrementExact as State
import DASHI.Physics.Foundations.CMP119AntigravityRichBrillouinRationalGaussianProjectionExact as Projection
import DASHI.Physics.Foundations.CMP119AntigravitySourceHistoryBishopUVViewExact as UV
import DASHI.Physics.YangMills.BalabanClayP3PhysicalOneStepTransferExact as P3
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4LiteralPlaquetteBetaEstimateExact as Literal
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- P3 REMAINDER IS FORCED BY MATCHED SOURCE RECURSION
--
-- Once P3's state/step carrier is the CMP109 UV history, exact recursion
-- already fixes its TOTAL increment.  The rich/literal one-loop decomposition
-- fixes the same total as
--
--   shell + (regular matching + beta_int).
--
-- Since P3 betaLogBlocking is the same shell, additive cancellation forces the
-- P3 remainder.  No independent remainder same-object witness is required.
------------------------------------------------------------------------

embeddedLiteralBetaIsSourceIncrement :
  ∀ {dataSet trajectory}
    (weld : LiteralToSource.LiteralPlaquetteCMP109UVSameObject dataSet trajectory)
    depth →
  Bishop._≃_
    (UV.embed (Flow.beta trajectory (suc depth)))
    (UV.embed (Literal.literalBetaStep dataSet depth))
embeddedLiteralBetaIsSourceIncrement weld depth =
  subst
    (λ selected →
      Bishop._≃_
        (UV.embed selected)
        (UV.embed (Literal.literalBetaStep _ depth)))
    (sym (LiteralToSource.literalBetaAtStepIsSourceSuccessorBeta weld depth))
    BishopP.≃-refl

targetTotalIsLiteralBeta :
  ∀ {dataSet rich recursion}
    (richAdd : ∀ left right →
      Bishop._≃_ (Rich.add rich left right) (Bishop._+_ left right))
    (shellSame : ∀ depth →
      Bishop._≃_
        (P3.betaLogBlocking recursion (suc depth))
        (Rich.scalarIntegral rich depth))
    (projection : Projection.RichBrillouinRationalGaussianProjection dataSet rich)
    depth →
  Bishop._≃_
    (Bishop._+_
      (P3.betaLogBlocking recursion (suc depth))
      (Rich.add rich
        (Rich.regularRemainder rich depth)
        (UV.embed (Literal.literalBetaInt dataSet depth))))
    (UV.embed (Literal.literalBetaStep dataSet depth))
targetTotalIsLiteralBeta {dataSet} {rich} {recursion}
    richAdd shellSame projection depth =
  BishopP.≃-trans
    (BishopP.+-cong
      (shellSame depth)
      (richAdd
        (Rich.regularRemainder rich depth)
        (UV.embed (Literal.literalBetaInt dataSet depth))))
    (BishopP.≃-trans
      (BishopP.≃-symm
        (BishopP.+-assoc
          (Rich.scalarIntegral rich depth)
          (Rich.regularRemainder rich depth)
          (UV.embed (Literal.literalBetaInt dataSet depth))))
      (BishopP.≃-trans
        (BishopP.+-cong
          (BishopP.≃-trans
            (BishopP.≃-symm
              (richAdd
                (Rich.scalarIntegral rich depth)
                (Rich.regularRemainder rich depth)))
            (BishopP.≃-symm
              (State.equalityAsBishopSetoid
                (Rich.coefficientDefinition rich depth))))
          BishopP.≃-refl)
        (BishopP.≃-trans
          (BishopP.+-cong
            (Projection.coefficientSameLiteralGaussian projection depth)
            BishopP.≃-refl)
          (BishopP.≃-symm
            (Carrier.bishopEmbedAdd
              (Literal.literalBetaZ dataSet depth)
              (Literal.literalBetaInt dataSet depth))))))

p3RemainderForced :
  ∀ {trajectory dataSet rich recursion}
    (state : State.P3StateRepresentsSourceUV trajectory recursion)
    (literalWeld : LiteralToSource.LiteralPlaquetteCMP109UVSameObject dataSet trajectory)
    (richAdd : ∀ left right →
      Bishop._≃_ (Rich.add rich left right) (Bishop._+_ left right))
    (shellSame : ∀ depth →
      Bishop._≃_
        (P3.betaLogBlocking recursion (suc depth))
        (Rich.scalarIntegral rich depth))
    (projection : Projection.RichBrillouinRationalGaussianProjection dataSet rich)
    depth →
  Bishop._≃_
    (P3.remainder recursion (suc depth))
    (Rich.add rich
      (Rich.regularRemainder rich depth)
      (UV.embed (Literal.literalBetaInt dataSet depth)))
p3RemainderForced {trajectory} {dataSet} {rich} {recursion}
    state literalWeld richAdd shellSame projection depth =
  let
    actualTotal :
      Bishop._≃_
        (Bishop._+_
          (P3.betaLogBlocking recursion (suc depth))
          (P3.remainder recursion (suc depth)))
        (UV.embed (Literal.literalBetaStep dataSet depth))
    actualTotal =
      BishopP.≃-trans
        (State.p3StateForcesTotalIncrement state (suc depth))
        (embeddedLiteralBetaIsSourceIncrement literalWeld depth)

    targetTotal :
      Bishop._≃_
        (Bishop._+_
          (P3.betaLogBlocking recursion (suc depth))
          (Rich.add rich
            (Rich.regularRemainder rich depth)
            (UV.embed (Literal.literalBetaInt dataSet depth))))
        (UV.embed (Literal.literalBetaStep dataSet depth))
    targetTotal =
      targetTotalIsLiteralBeta richAdd shellSame projection depth

    sameOuter :
      Bishop._≃_
        (Bishop._+_
          (P3.betaLogBlocking recursion (suc depth))
          (P3.remainder recursion (suc depth)))
        (Bishop._+_
          (P3.betaLogBlocking recursion (suc depth))
          (Rich.add rich
            (Rich.regularRemainder rich depth)
            (UV.embed (Literal.literalBetaInt dataSet depth))))
    sameOuter =
      BishopP.≃-trans actualTotal (BishopP.≃-symm targetTotal)
  in
  Cancel.bishopAddLeftCancel sameOuter

independentP3RemainderWitnessRequired : Agda.Builtin.Bool.Bool
independentP3RemainderWitnessRequired = Agda.Builtin.Bool.false

p3RichRemainderForcedCompilerLevel : ProofLevel
p3RichRemainderForcedCompilerLevel = machineChecked
