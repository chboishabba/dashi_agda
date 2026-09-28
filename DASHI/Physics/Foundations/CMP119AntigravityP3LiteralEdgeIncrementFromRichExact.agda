{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityP3LiteralEdgeIncrementFromRichExact where

open import Agda.Builtin.Nat using (Nat; suc)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Physics.Closure.NSTriadKNMurrayBishopDirectCanonicalCarrier as Carrier
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
-- LOCAL POSITIVE-EDGE INCREMENT COMPILER
--
-- This theorem is deliberately STATE-FREE.  It does not assume
--
--   P3.inverseCouplingSq k ~= source u_k
--
-- at any depth.  Instead it uses only the local physical decomposition of the
-- increment on one edge:
--
--   P3 betaLogBlocking      = rich singular Brillouin shell
--   P3 remainder            = rich regular matching + literal interaction,
--
-- plus the already-owned rich coefficient -> rational literal beta_Z weld.
--
-- Hence the positive-edge P3 total increment is the literal beta step without
-- any all-depth state/history hypothesis.
------------------------------------------------------------------------

record CanonicalP3LiteralEdgeIncrementInputs
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

    p3RemainderIsLocalPhysicalRemainder :
      ∀ depth →
      Bishop._≃_
        (P3.remainder (SU2.recursion running) (suc depth))
        (Rich.add rich
          (Rich.regularRemainder rich depth)
          (UV.embed (Literal.literalBetaInt dataSet depth)))

open CanonicalP3LiteralEdgeIncrementInputs public

richCoefficientAsBishopShellPlusRegular :
  ∀ {dataSet rich running}
    (inputs : CanonicalP3LiteralEdgeIncrementInputs dataSet rich running)
    depth →
  Bishop._≃_
    (Bishop._+_
      (Rich.scalarIntegral rich depth)
      (Rich.regularRemainder rich depth))
    (Rich.coefficient rich depth)
richCoefficientAsBishopShellPlusRegular {rich = rich} inputs depth =
  BishopP.≃-trans
    (BishopP.≃-symm
      (richAddIsBishopAdd inputs
        (Rich.scalarIntegral rich depth)
        (Rich.regularRemainder rich depth)))
    (BishopP.≃-symm
      (CanonicalRich.equalityAsBishopSetoid
        (Rich.coefficientDefinition rich depth)))

successorTotalIncrementSameLiteral :
  ∀ {dataSet rich running}
    (inputs : CanonicalP3LiteralEdgeIncrementInputs dataSet rich running)
    depth →
  Bishop._≃_
    (Bishop._+_
      (P3.betaLogBlocking (SU2.recursion running) (suc depth))
      (P3.remainder (SU2.recursion running) (suc depth)))
    (UV.embed (Literal.literalBetaStep dataSet depth))
successorTotalIncrementSameLiteral
    {dataSet = dataSet} {rich = rich} {running = running}
    inputs depth =
  BishopP.≃-trans
    (BishopP.+-cong
      (CanonicalRich.p3SuccessorGaussianSameRichEdgeIntegral
        (richNormalization inputs) depth)
      (p3RemainderIsLocalPhysicalRemainder inputs depth))
    (BishopP.≃-trans
      (BishopP.+-cong
        BishopP.≃-refl
        (richAddIsBishopAdd inputs
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
            (richCoefficientAsBishopShellPlusRegular inputs depth)
            BishopP.≃-refl)
          (BishopP.≃-trans
            (BishopP.+-cong
              (Projection.coefficientSameLiteralGaussian
                (gaussianProjection inputs) depth)
              BishopP.≃-refl)
            (BishopP.≃-symm
              (Carrier.bishopEmbedAdd
                (Literal.literalBetaZ dataSet depth)
                (Literal.literalBetaInt dataSet depth)))))))

positiveEdgeStateHistoryRequired : Agda.Builtin.Bool.Bool
positiveEdgeStateHistoryRequired = Agda.Builtin.Bool.false

independentTotalIncrementWitnessRequired : Agda.Builtin.Bool.Bool
independentTotalIncrementWitnessRequired = Agda.Builtin.Bool.false

localP3RemainderPhysicalIdentificationStillRequired : Agda.Builtin.Bool.Bool
localP3RemainderPhysicalIdentificationStillRequired = Agda.Builtin.Bool.true

p3LiteralEdgeIncrementFromRichCompilerLevel : ProofLevel
p3LiteralEdgeIncrementFromRichCompilerLevel = machineChecked

p3LocalPhysicalRemainderProducerLevel : ProofLevel
p3LocalPhysicalRemainderProducerLevel = conditional
