{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityP3LiteralEdgeIncrementMinCutExact where

open import Agda.Builtin.Nat using (Nat; suc)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Physics.Closure.NSTriadKNMurrayBishopDirectCanonicalCarrier as Carrier
import DASHI.Physics.Foundations.CMP119AntigravityBishopMatchedRecursionResidualExact as Cancel
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopRichBrillouinUVEdgeExact as CanonicalRich
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact as SU2
import DASHI.Physics.Foundations.CMP119AntigravityRichBrillouinRationalGaussianProjectionExact as Projection
import DASHI.Physics.Foundations.CMP119AntigravitySourceHistoryBishopUVViewExact as UV
import DASHI.Physics.YangMills.BalabanClayP3PhysicalOneStepTransferExact as P3
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4LiteralPlaquetteBetaEstimateExact as Literal
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- TRUE POSITIVE-EDGE MIN-CUT
--
-- Keep already-owned rich geometry separate from the only P3-specific local
-- payment.  Under this geometry, the following two statements are equivalent:
--
--   P3 betaLogBlocking + P3 remainder = embedded literal beta step
--
-- and
--
--   P3 remainder = rich regular remainder + embedded literal interaction.
--
-- Thus the positive-edge total-increment witness is not an independent S4
-- payment.  The irreducible P3-specific edge seam is the local remainder
-- producer itself.
------------------------------------------------------------------------

record CanonicalP3LiteralEdgeGeometry
    (dataSet : Plaquette.PhysicalRunningCouplingData Nat)
    (rich : Rich.LiteralBrillouinIntegralPhysicalData Nat Bishop.ℝ)
    (running : SU2.CanonicalBishopSU2RunningInputs Nat) : Set₁ where
  field
    richNormalization :
      CanonicalRich.CanonicalBishopRichBrillouinUVEdgeNormalization rich running

    richAddIsBishopAdd :
      ∀ left right →
      Bishop._≃_
        (Rich.add rich left right)
        (Bishop._+_ left right)

    gaussianProjection :
      Projection.RichBrillouinRationalGaussianProjection dataSet rich

open CanonicalP3LiteralEdgeGeometry public

richCoefficientAsBishopShellPlusRegular :
  ∀ {dataSet rich running}
    (geometry : CanonicalP3LiteralEdgeGeometry dataSet rich running)
    depth →
  Bishop._≃_
    (Bishop._+_
      (Rich.scalarIntegral rich depth)
      (Rich.regularRemainder rich depth))
    (Rich.coefficient rich depth)
richCoefficientAsBishopShellPlusRegular {rich = rich} geometry depth =
  BishopP.≃-trans
    (BishopP.≃-symm
      (richAddIsBishopAdd geometry
        (Rich.scalarIntegral rich depth)
        (Rich.regularRemainder rich depth)))
    (BishopP.≃-symm
      (CanonicalRich.equalityAsBishopSetoid
        (Rich.coefficientDefinition rich depth)))

targetTotalWithLocalPhysicalRemainder :
  ∀ {dataSet rich running}
    (geometry : CanonicalP3LiteralEdgeGeometry dataSet rich running)
    depth →
  Bishop._≃_
    (Bishop._+_
      (P3.betaLogBlocking (SU2.recursion running) (suc depth))
      (Rich.add rich
        (Rich.regularRemainder rich depth)
        (UV.embed (Literal.literalBetaInt dataSet depth))))
    (UV.embed (Literal.literalBetaStep dataSet depth))
targetTotalWithLocalPhysicalRemainder
    {dataSet = dataSet} {rich = rich} {running = running}
    geometry depth =
  BishopP.≃-trans
    (BishopP.+-cong
      (CanonicalRich.p3SuccessorGaussianSameRichEdgeIntegral
        (richNormalization geometry) depth)
      BishopP.≃-refl)
    (BishopP.≃-trans
      (BishopP.+-cong
        BishopP.≃-refl
        (richAddIsBishopAdd geometry
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
            (richCoefficientAsBishopShellPlusRegular geometry depth)
            BishopP.≃-refl)
          (BishopP.≃-trans
            (BishopP.+-cong
              (Projection.coefficientSameLiteralGaussian
                (gaussianProjection geometry) depth)
              BishopP.≃-refl)
            (BishopP.≃-symm
              (Carrier.bishopEmbedAdd
                (Literal.literalBetaZ dataSet depth)
                (Literal.literalBetaInt dataSet depth)))))))

remainderImpliesTotalIncrement :
  ∀ {dataSet rich running}
    (geometry : CanonicalP3LiteralEdgeGeometry dataSet rich running)
    depth →
  Bishop._≃_
    (P3.remainder (SU2.recursion running) (suc depth))
    (Rich.add rich
      (Rich.regularRemainder rich depth)
      (UV.embed (Literal.literalBetaInt dataSet depth))) →
  Bishop._≃_
    (Bishop._+_
      (P3.betaLogBlocking (SU2.recursion running) (suc depth))
      (P3.remainder (SU2.recursion running) (suc depth)))
    (UV.embed (Literal.literalBetaStep dataSet depth))
remainderImpliesTotalIncrement geometry depth remainderSame =
  BishopP.≃-trans
    (BishopP.+-cong BishopP.≃-refl remainderSame)
    (targetTotalWithLocalPhysicalRemainder geometry depth)

totalIncrementImpliesRemainder :
  ∀ {dataSet rich running}
    (geometry : CanonicalP3LiteralEdgeGeometry dataSet rich running)
    depth →
  Bishop._≃_
    (Bishop._+_
      (P3.betaLogBlocking (SU2.recursion running) (suc depth))
      (P3.remainder (SU2.recursion running) (suc depth)))
    (UV.embed (Literal.literalBetaStep dataSet depth)) →
  Bishop._≃_
    (P3.remainder (SU2.recursion running) (suc depth))
    (Rich.add rich
      (Rich.regularRemainder rich depth)
      (UV.embed (Literal.literalBetaInt dataSet depth)))
totalIncrementImpliesRemainder geometry depth totalSame =
  Cancel.bishopAddLeftCancel
    (BishopP.≃-trans
      totalSame
      (BishopP.≃-symm
        (targetTotalWithLocalPhysicalRemainder geometry depth)))

record PositiveEdgeIncrementIffLocalRemainder
    {dataSet : Plaquette.PhysicalRunningCouplingData Nat}
    {rich : Rich.LiteralBrillouinIntegralPhysicalData Nat Bishop.ℝ}
    {running : SU2.CanonicalBishopSU2RunningInputs Nat}
    (geometry : CanonicalP3LiteralEdgeGeometry dataSet rich running)
    (depth : Nat) : Set₁ where
  field
    totalToRemainder :
      Bishop._≃_
        (Bishop._+_
          (P3.betaLogBlocking (SU2.recursion running) (suc depth))
          (P3.remainder (SU2.recursion running) (suc depth)))
        (UV.embed (Literal.literalBetaStep dataSet depth)) →
      Bishop._≃_
        (P3.remainder (SU2.recursion running) (suc depth))
        (Rich.add rich
          (Rich.regularRemainder rich depth)
          (UV.embed (Literal.literalBetaInt dataSet depth)))

    remainderToTotal :
      Bishop._≃_
        (P3.remainder (SU2.recursion running) (suc depth))
        (Rich.add rich
          (Rich.regularRemainder rich depth)
          (UV.embed (Literal.literalBetaInt dataSet depth))) →
      Bishop._≃_
        (Bishop._+_
          (P3.betaLogBlocking (SU2.recursion running) (suc depth))
          (P3.remainder (SU2.recursion running) (suc depth)))
        (UV.embed (Literal.literalBetaStep dataSet depth))

positiveEdgeIncrementIffLocalRemainder :
  ∀ {dataSet rich running}
    (geometry : CanonicalP3LiteralEdgeGeometry dataSet rich running)
    depth →
  PositiveEdgeIncrementIffLocalRemainder geometry depth
positiveEdgeIncrementIffLocalRemainder geometry depth = record
  { PositiveEdgeIncrementIffLocalRemainder.totalToRemainder =
      totalIncrementImpliesRemainder geometry depth
  ; PositiveEdgeIncrementIffLocalRemainder.remainderToTotal =
      remainderImpliesTotalIncrement geometry depth
  }

directPositiveEdgeIncrementWitnessIsIndependent : Agda.Builtin.Bool.Bool
directPositiveEdgeIncrementWitnessIsIndependent = Agda.Builtin.Bool.false

localP3RemainderIsExactEdgePayment : Agda.Builtin.Bool.Bool
localP3RemainderIsExactEdgePayment = Agda.Builtin.Bool.true

p3LiteralEdgeIncrementMinCutCompilerLevel : ProofLevel
p3LiteralEdgeIncrementMinCutCompilerLevel = machineChecked
