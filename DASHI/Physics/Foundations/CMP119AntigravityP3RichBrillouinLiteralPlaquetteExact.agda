{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityP3RichBrillouinLiteralPlaquetteExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (0ℚ)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Physics.Closure.NSTriadKNMurrayBishopDirectCanonicalCarrier as Carrier
import DASHI.Physics.Foundations.CMP119AntigravityP3LiteralPlaquetteCMP109SameObjectExact as P3Literal
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact as SU2Running
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopRichBrillouinGaussianExact as CanonicalRich
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
-- CANONICAL-RUNNING CONSTRUCTOR
--
-- On the canonical Bishop route the P3 -> rich Gaussian edge is not an
-- independent physical premise: it follows from the two explicit formulas.
-- The remaining cross-carrier Gaussian payment is only
--
--   rich scalarIntegral ~= embed(rational literal beta_Z).
------------------------------------------------------------------------

record CanonicalRunningRichLiteralPlaquetteSplit
    (dataSet : Plaquette.PhysicalRunningCouplingData Nat)
    (rich : Rich.LiteralBrillouinIntegralPhysicalData Nat Bishop.ℝ)
    (running : SU2Running.CanonicalBishopSU2RunningInputs Nat) : Set₁ where
  field
    richNormalization :
      CanonicalRich.CanonicalBishopRichBrillouinNormalization rich running

    addIsBishopAdd :
      ∀ left right →
      Bishop._≃_
        (P3.add (SU2Running.recursion running) left right)
        (Bishop._+_ left right)

    inverseCouplingSameLiteral :
      ∀ depth →
      Bishop._≃_
        (P3.inverseCouplingSq (SU2Running.recursion running) depth)
        (UV.embed (Plaquette.inverseCouplingSq dataSet depth))

    nextScaleIsUVPredecessor :
      ∀ depth →
      P3.nextScale (SU2Running.recursion running) depth ≡ UV.uvNext depth

    zeroTotalIncrementSame :
      Bishop._≃_
        (Bishop._+_
          (P3.betaLogBlocking (SU2Running.recursion running) zero)
          (P3.remainder (SU2Running.recursion running) zero))
        (UV.embed 0ℚ)

    richScalarIntegralSameLiteralGaussian :
      ∀ depth →
      Bishop._≃_
        (Rich.scalarIntegral rich (suc depth))
        (UV.embed (Literal.literalBetaZ dataSet (suc depth)))

    remainderSameLiteralInteraction :
      ∀ depth →
      Bishop._≃_
        (P3.remainder (SU2Running.recursion running) (suc depth))
        (UV.embed (Literal.literalBetaInt dataSet (suc depth)))

open CanonicalRunningRichLiteralPlaquetteSplit public

canonicalRunningAsRichBrillouinBridge :
  ∀ {dataSet rich running} →
  CanonicalRunningRichLiteralPlaquetteSplit dataSet rich running →
  P3RepresentsRichBrillouinLiteralPlaquetteSplit
    dataSet rich (SU2Running.recursion running)
canonicalRunningAsRichBrillouinBridge inputs = record
  { P3RepresentsRichBrillouinLiteralPlaquetteSplit.addIsBishopAdd =
      CanonicalRunningRichLiteralPlaquetteSplit.addIsBishopAdd inputs

  ; P3RepresentsRichBrillouinLiteralPlaquetteSplit.inverseCouplingSameLiteral =
      CanonicalRunningRichLiteralPlaquetteSplit.inverseCouplingSameLiteral inputs

  ; P3RepresentsRichBrillouinLiteralPlaquetteSplit.nextScaleIsUVPredecessor =
      CanonicalRunningRichLiteralPlaquetteSplit.nextScaleIsUVPredecessor inputs

  ; P3RepresentsRichBrillouinLiteralPlaquetteSplit.zeroTotalIncrementSame =
      CanonicalRunningRichLiteralPlaquetteSplit.zeroTotalIncrementSame inputs

  ; P3RepresentsRichBrillouinLiteralPlaquetteSplit.p3GaussianSameRichScalarIntegral =
      CanonicalRich.p3GaussianSameRichScalarIntegral
        (richNormalization inputs)

  ; P3RepresentsRichBrillouinLiteralPlaquetteSplit.richScalarIntegralSameLiteralGaussian =
      CanonicalRunningRichLiteralPlaquetteSplit.richScalarIntegralSameLiteralGaussian inputs

  ; P3RepresentsRichBrillouinLiteralPlaquetteSplit.remainderSameLiteralInteraction =
      CanonicalRunningRichLiteralPlaquetteSplit.remainderSameLiteralInteraction inputs
  }

canonicalRunningAsLiteralSplit :
  ∀ {dataSet rich running} →
  CanonicalRunningRichLiteralPlaquetteSplit dataSet rich running →
  P3Literal.P3RepresentsLiteralPlaquetteSplitUVView
    dataSet (SU2Running.recursion running)
canonicalRunningAsLiteralSplit inputs =
  richBrillouinViewAsLiteralSplit
    (canonicalRunningAsRichBrillouinBridge inputs)

independentP3ToRichGaussianWitnessRequiredOnCanonicalRoute :
  Agda.Builtin.Bool.Bool
independentP3ToRichGaussianWitnessRequiredOnCanonicalRoute =
  Agda.Builtin.Bool.false

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
