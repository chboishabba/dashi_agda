{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityP3RichBrillouinLiteralPlaquetteExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (0ℚ)
open import Relation.Binary.PropositionalEquality using (subst)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Physics.Closure.NSTriadKNMurrayBishopDirectCanonicalCarrier as Carrier
import DASHI.Physics.Foundations.CMP119AntigravityP3LiteralPlaquetteCMP109SameObjectExact as P3Literal
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact as SU2Running
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopRichBrillouinUVEdgeExact as CanonicalRich
import DASHI.Physics.Foundations.CMP119AntigravityRichBrillouinRationalGaussianProjectionExact as Projection
import DASHI.Physics.Foundations.CMP119AntigravitySourceHistoryBishopUVViewExact as UV
import DASHI.Physics.YangMills.BalabanClayP3PhysicalOneStepTransferExact as P3
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4LiteralPlaquetteBetaEstimateExact as Literal
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- CORRECT RICH DECOMPOSITION
--
-- The rich one-loop carrier separates
--
--   coefficient = scalarIntegral + regularRemainder.
--
-- P3 betaLogBlocking is the universal logarithmic shell `scalarIntegral`.
-- Therefore the P3 remainder must carry BOTH the regular one-loop matching
-- remainder and the finite-g literal interaction remainder.
--
-- This module compiles only the TOTAL P3 increment to the literal plaquette
-- beta step.  It intentionally does NOT manufacture a split-level theorem
-- identifying P3 betaLogBlocking with the full literal beta_Z.
------------------------------------------------------------------------

equalityAsBishopSetoid :
  ∀ {left right : Bishop.ℝ} →
  left ≡ right → Bishop._≃_ left right
equalityAsBishopSetoid {left} equality =
  subst (λ selected → Bishop._≃_ left selected) equality BishopP.≃-refl

record P3RepresentsRichBrillouinLiteralPlaquette
    (dataSet : Plaquette.PhysicalRunningCouplingData Nat)
    (rich : Rich.LiteralBrillouinIntegralPhysicalData Nat Bishop.ℝ)
    (recursion : P3.RunningCouplingRecursion Nat Bishop.ℝ) : Set₁ where
  field
    addIsBishopAdd :
      ∀ left right →
      Bishop._≃_
        (P3.add recursion left right)
        (Bishop._+_ left right)

    richAddIsBishopAdd :
      ∀ left right →
      Bishop._≃_
        (Rich.add rich left right)
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

    p3GaussianSameRichScalarIntegral :
      ∀ depth →
      Bishop._≃_
        (P3.betaLogBlocking recursion (suc depth))
        (Rich.scalarIntegral rich depth)

    gaussianProjection :
      Projection.RichBrillouinRationalGaussianProjection dataSet rich

    p3RemainderSameRichRegularPlusLiteralInteraction :
      ∀ depth →
      Bishop._≃_
        (P3.remainder recursion (suc depth))
        (Rich.add rich
          (Rich.regularRemainder rich depth)
          (UV.embed (Literal.literalBetaInt dataSet depth)))

open P3RepresentsRichBrillouinLiteralPlaquette public

richCoefficientAsBishopShellPlusRegular :
  ∀ {dataSet rich recursion}
    (bridge : P3RepresentsRichBrillouinLiteralPlaquette dataSet rich recursion)
    depth →
  Bishop._≃_
    (Bishop._+_
      (Rich.scalarIntegral rich depth)
      (Rich.regularRemainder rich depth))
    (Rich.coefficient rich depth)
richCoefficientAsBishopShellPlusRegular {rich = rich} bridge depth =
  BishopP.≃-trans
    (BishopP.≃-symm
      (richAddIsBishopAdd bridge
        (Rich.scalarIntegral rich depth)
        (Rich.regularRemainder rich depth)))
    (BishopP.≃-symm
      (equalityAsBishopSetoid
        (Rich.coefficientDefinition rich depth)))

successorTotalIncrementSameLiteral :
  ∀ {dataSet rich recursion}
    (bridge : P3RepresentsRichBrillouinLiteralPlaquette dataSet rich recursion)
    depth →
  Bishop._≃_
    (Bishop._+_
      (P3.betaLogBlocking recursion (suc depth))
      (P3.remainder recursion (suc depth)))
    (UV.embed (Literal.literalBetaStep dataSet depth))
successorTotalIncrementSameLiteral
    {dataSet = dataSet} {rich = rich} {recursion = recursion}
    bridge depth =
  BishopP.≃-trans
    (BishopP.+-cong
      (p3GaussianSameRichScalarIntegral bridge depth)
      (p3RemainderSameRichRegularPlusLiteralInteraction bridge depth))
    (BishopP.≃-trans
      (BishopP.+-cong
        BishopP.≃-refl
        (richAddIsBishopAdd bridge
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
            (richCoefficientAsBishopShellPlusRegular bridge depth)
            BishopP.≃-refl)
          (BishopP.≃-trans
            (BishopP.+-cong
              (Projection.coefficientSameLiteralGaussian
                (gaussianProjection bridge) depth)
              BishopP.≃-refl)
            (BishopP.≃-symm
              (Carrier.bishopEmbedAdd
                (Literal.literalBetaZ dataSet depth)
                (Literal.literalBetaInt dataSet depth))))))))

asLiteralTotalView :
  ∀ {dataSet rich recursion} →
  P3RepresentsRichBrillouinLiteralPlaquette dataSet rich recursion →
  P3Literal.P3RepresentsLiteralPlaquetteUVView dataSet recursion
asLiteralTotalView bridge = record
  { P3Literal.P3RepresentsLiteralPlaquetteUVView.addIsBishopAdd =
      addIsBishopAdd bridge
  ; P3Literal.P3RepresentsLiteralPlaquetteUVView.inverseCouplingSameLiteral =
      inverseCouplingSameLiteral bridge
  ; P3Literal.P3RepresentsLiteralPlaquetteUVView.nextScaleIsUVPredecessor =
      nextScaleIsUVPredecessor bridge
  ; P3Literal.P3RepresentsLiteralPlaquetteUVView.zeroTotalIncrementSame =
      zeroTotalIncrementSame bridge
  ; P3Literal.P3RepresentsLiteralPlaquetteUVView.successorTotalIncrementSameLiteral =
      successorTotalIncrementSameLiteral bridge
  }

record CanonicalRunningRichLiteralPlaquette
    (dataSet : Plaquette.PhysicalRunningCouplingData Nat)
    (rich : Rich.LiteralBrillouinIntegralPhysicalData Nat Bishop.ℝ)
    (running : SU2Running.CanonicalBishopSU2RunningInputs Nat) : Set₁ where
  field
    richNormalization :
      CanonicalRich.CanonicalBishopRichBrillouinUVEdgeNormalization rich running

    addIsBishopAdd :
      ∀ left right →
      Bishop._≃_
        (P3.add (SU2Running.recursion running) left right)
        (Bishop._+_ left right)

    richAddIsBishopAdd :
      ∀ left right →
      Bishop._≃_
        (Rich.add rich left right)
        (Bishop._+_ left right)

    inverseCouplingSameLiteral :
      ∀ depth →
      Bishop._≃_
        (P3.inverseCouplingSq (SU2Running.recursion running) depth)
        (UV.embed (Plaquette.nextInverseCouplingSq dataSet depth))

    nextScaleIsUVPredecessor :
      ∀ depth →
      P3.nextScale (SU2Running.recursion running) depth ≡ UV.uvNext depth

    zeroTotalIncrementSame :
      Bishop._≃_
        (Bishop._+_
          (P3.betaLogBlocking (SU2Running.recursion running) zero)
          (P3.remainder (SU2Running.recursion running) zero))
        (UV.embed 0ℚ)

    gaussianProjection :
      Projection.RichBrillouinRationalGaussianProjection dataSet rich

    p3RemainderSameRichRegularPlusLiteralInteraction :
      ∀ depth →
      Bishop._≃_
        (P3.remainder (SU2Running.recursion running) (suc depth))
        (Rich.add rich
          (Rich.regularRemainder rich depth)
          (UV.embed (Literal.literalBetaInt dataSet depth)))

open CanonicalRunningRichLiteralPlaquette public

canonicalRunningAsRichBridge :
  ∀ {dataSet rich running} →
  CanonicalRunningRichLiteralPlaquette dataSet rich running →
  P3RepresentsRichBrillouinLiteralPlaquette
    dataSet rich (SU2Running.recursion running)
canonicalRunningAsRichBridge inputs = record
  { P3RepresentsRichBrillouinLiteralPlaquette.addIsBishopAdd =
      CanonicalRunningRichLiteralPlaquette.addIsBishopAdd inputs
  ; P3RepresentsRichBrillouinLiteralPlaquette.richAddIsBishopAdd =
      CanonicalRunningRichLiteralPlaquette.richAddIsBishopAdd inputs
  ; P3RepresentsRichBrillouinLiteralPlaquette.inverseCouplingSameLiteral =
      CanonicalRunningRichLiteralPlaquette.inverseCouplingSameLiteral inputs
  ; P3RepresentsRichBrillouinLiteralPlaquette.nextScaleIsUVPredecessor =
      CanonicalRunningRichLiteralPlaquette.nextScaleIsUVPredecessor inputs
  ; P3RepresentsRichBrillouinLiteralPlaquette.zeroTotalIncrementSame =
      CanonicalRunningRichLiteralPlaquette.zeroTotalIncrementSame inputs
  ; P3RepresentsRichBrillouinLiteralPlaquette.p3GaussianSameRichScalarIntegral =
      CanonicalRich.p3SuccessorGaussianSameRichEdgeIntegral
        (richNormalization inputs)
  ; P3RepresentsRichBrillouinLiteralPlaquette.gaussianProjection =
      CanonicalRunningRichLiteralPlaquette.gaussianProjection inputs
  ; P3RepresentsRichBrillouinLiteralPlaquette.p3RemainderSameRichRegularPlusLiteralInteraction =
      CanonicalRunningRichLiteralPlaquette.p3RemainderSameRichRegularPlusLiteralInteraction inputs
  }

canonicalRunningAsLiteralTotal :
  ∀ {dataSet rich running} →
  CanonicalRunningRichLiteralPlaquette dataSet rich running →
  P3Literal.P3RepresentsLiteralPlaquetteUVView
    dataSet (SU2Running.recursion running)
canonicalRunningAsLiteralTotal inputs =
  asLiteralTotalView (canonicalRunningAsRichBridge inputs)

splitLevelP3GaussianToFullLiteralBetaZRequired : Agda.Builtin.Bool.Bool
splitLevelP3GaussianToFullLiteralBetaZRequired = Agda.Builtin.Bool.false

richRegularRemainderMustJoinP3Remainder : Agda.Builtin.Bool.Bool
richRegularRemainderMustJoinP3Remainder = Agda.Builtin.Bool.true

richBrillouinLiteralPlaquetteCompilerLevel : ProofLevel
richBrillouinLiteralPlaquetteCompilerLevel = machineChecked

richBrillouinLiteralPlaquettePhysicalSameObjectLevel : ProofLevel
richBrillouinLiteralPlaquettePhysicalSameObjectLevel = conditional
