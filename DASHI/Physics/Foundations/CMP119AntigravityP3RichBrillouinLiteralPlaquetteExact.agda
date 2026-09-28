{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityP3RichBrillouinLiteralPlaquetteExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (0ℚ)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Physics.Closure.NSTriadKNMurrayBishopDirectCanonicalCarrier as Carrier
import DASHI.Physics.Foundations.CMP119AntigravityP3LiteralPlaquetteCMP109SameObjectExact as P3Literal
import DASHI.Physics.Foundations.CMP119AntigravitySourceHistoryBishopUVViewExact as UV
import DASHI.Physics.YangMills.BalabanClayP3PhysicalOneStepTransferExact as P3
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4LiteralPlaquetteBetaEstimateExact as Literal
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- P3 -> RICH T4 BRILLOUIN GAUSSIAN -> RATIONAL LITERAL PLAQUETTE
--
-- The rich T4 carrier keeps the physical Gaussian shell coefficient in its
-- native Scalar and retains inversePiSquared and logBlocking explicitly.
-- The older rational plaquette carrier is still the object already welded to
-- CMP109.  The shortest safe bridge therefore uses the SAME P3 Gaussian field
-- as the common apex:
--
--   canonical Bishop convention
--            |
--            v
--      P3.betaLogBlocking
--          /       \
--         v         v
-- rich scalarIntegral   embed(rational beta_Z)
--
-- We do not manufacture a pi^2 rescaling of either log coordinate.  The only
-- cross-carrier source payment is that the rich shell integral and the older
-- rational beta_Z are two representations of the same localized Gaussian
-- coefficient.
------------------------------------------------------------------------

record P3RepresentsRichBrillouinLiteralPlaquetteSplit
    (dataSet : Plaquette.PhysicalRunningCouplingData Nat)
    (rich :
      Rich.LiteralBrillouinIntegralPhysicalData Nat Bishop.ℝ)
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
        (UV.embed (Plaquette.inverseCouplingSq dataSet depth))

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
        (Rich.scalarIntegral rich (suc depth))

    richScalarIntegralSameLiteralGaussian :
      ∀ depth →
      Bishop._≃_
        (Rich.scalarIntegral rich (suc depth))
        (UV.embed (Literal.literalBetaZ dataSet (suc depth)))

    remainderSameLiteralInteraction :
      ∀ depth →
      Bishop._≃_
        (P3.remainder recursion (suc depth))
        (UV.embed (Literal.literalBetaInt dataSet (suc depth)))

open P3RepresentsRichBrillouinLiteralPlaquetteSplit public

richBrillouinViewAsLiteralSplit :
  ∀ {dataSet rich recursion} →
  P3RepresentsRichBrillouinLiteralPlaquetteSplit
    dataSet rich recursion →
  P3Literal.P3RepresentsLiteralPlaquetteSplitUVView
    dataSet recursion
richBrillouinViewAsLiteralSplit bridge = record
  { P3Literal.P3RepresentsLiteralPlaquetteSplitUVView.addIsBishopAdd =
      addIsBishopAdd bridge

  ; P3Literal.P3RepresentsLiteralPlaquetteSplitUVView.inverseCouplingSameLiteral =
      inverseCouplingSameLiteral bridge

  ; P3Literal.P3RepresentsLiteralPlaquetteSplitUVView.nextScaleIsUVPredecessor =
      nextScaleIsUVPredecessor bridge

  ; P3Literal.P3RepresentsLiteralPlaquetteSplitUVView.zeroTotalIncrementSame =
      zeroTotalIncrementSame bridge

  ; P3Literal.P3RepresentsLiteralPlaquetteSplitUVView.betaLogBlockingSameLiteralGaussian =
      λ depth →
        BishopP.≃-trans
          (p3GaussianSameRichScalarIntegral bridge depth)
          (richScalarIntegralSameLiteralGaussian bridge depth)

  ; P3Literal.P3RepresentsLiteralPlaquetteSplitUVView.remainderSameLiteralInteraction =
      remainderSameLiteralInteraction bridge
  }

richBrillouinViewAsLiteralTotal :
  ∀ {dataSet rich recursion} →
  P3RepresentsRichBrillouinLiteralPlaquetteSplit
    dataSet rich recursion →
  P3Literal.P3RepresentsLiteralPlaquetteUVView
    dataSet recursion
richBrillouinViewAsLiteralTotal bridge =
  P3Literal.splitViewAsTotalView
    (richBrillouinViewAsLiteralSplit bridge)

------------------------------------------------------------------------
-- FRONTIER RECUT
------------------------------------------------------------------------

normalizedLogCoordinateRequiredOnRichBypass :
  Agda.Builtin.Bool.Bool
normalizedLogCoordinateRequiredOnRichBypass =
  Agda.Builtin.Bool.false

richToRationalGaussianSameObjectStillRequired :
  Agda.Builtin.Bool.Bool
richToRationalGaussianSameObjectStillRequired =
  Agda.Builtin.Bool.true

p3ToRichGaussianSameObjectStillRequired :
  Agda.Builtin.Bool.Bool
p3ToRichGaussianSameObjectStillRequired =
  Agda.Builtin.Bool.true

richBrillouinLiteralPlaquetteCompilerLevel : ProofLevel
richBrillouinLiteralPlaquetteCompilerLevel = machineChecked

richBrillouinLiteralPlaquettePhysicalSameObjectLevel : ProofLevel
richBrillouinLiteralPlaquettePhysicalSameObjectLevel = conditional
