{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCanonicalS4RichProjectionMaxCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; 0ℚ)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact as SU2
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopRichBrillouinUVEdgeExact as CanonicalRich
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalRowABetaDrivenStateExact as RowAState
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalS4SameObjectPackageExact as S4
import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteCMP109UVSameObjectExact as LiteralToSource
import DASHI.Physics.Foundations.CMP119AntigravityP3LiteralPlaquetteCMP109SameObjectExact as P3Literal
import DASHI.Physics.Foundations.CMP119AntigravityP3RichBrillouinLiteralPlaquetteExact as P3Rich
import DASHI.Physics.Foundations.CMP119AntigravityRichBrillouinRationalGaussianProjectionExact as Projection
import DASHI.Physics.Foundations.CMP119AntigravitySourceHistoryBishopUVViewExact as UV
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaFlow
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact as Split
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanClayP3PhysicalOneStepTransferExact as P3
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4LiteralPlaquetteBetaEstimateExact as Literal
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- CANONICAL S4 RICH-PROJECTION MAX CUT
--
-- The canonical Bishop formula determines
--   P3.betaLogBlocking ~= rich.scalarIntegral
-- from richNormalization.
--
-- Therefore the only Gaussian cross-carrier source payment is
--   rich.scalarIntegral ~= embed(rational literal beta_Z),
-- carried by gaussianProjection.
------------------------------------------------------------------------

record CanonicalS4RichProjectionMaxCut
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {split : Split.FiniteLatticeBetaSplit trajectory}
    (inputs : BetaFlow.BetaDrivenCompleteDensityInputs {trajectory} {split})
    (rowA : RowA.FiniteQuarticResponseConstants)
    (smallFieldCap largeFieldCap covarianceCap : ℚ)
    (dataSet : Plaquette.PhysicalRunningCouplingData Nat)
    (rich : Rich.LiteralBrillouinIntegralPhysicalData Nat Bishop.ℝ) : Set₂ where
  field
    betaCoordinates :
      RowAState.CanonicalRowABetaDrivenCoordinates
        inputs rowA smallFieldCap largeFieldCap covarianceCap

    bishopRunning :
      SU2.CanonicalBishopSU2RunningInputs Nat

    richNormalization :
      CanonicalRich.CanonicalBishopRichBrillouinUVEdgeNormalization
        rich bishopRunning

    gaussianProjection :
      Projection.RichBrillouinRationalGaussianProjection dataSet rich

    addIsBishopAdd :
      ∀ left right →
      Bishop._≃_
        (P3.add (SU2.recursion bishopRunning) left right)
        (Bishop._+_ left right)

    inverseCouplingSameLiteral :
      ∀ depth →
      Bishop._≃_
        (P3.inverseCouplingSq (SU2.recursion bishopRunning) depth)
        (UV.embed (Plaquette.inverseCouplingSq dataSet depth))

    nextScaleIsUVPredecessor :
      ∀ depth →
      P3.nextScale (SU2.recursion bishopRunning) depth ≡ UV.uvNext depth

    zeroTotalIncrementSame :
      Bishop._≃_
        (Bishop._+_
          (P3.betaLogBlocking (SU2.recursion bishopRunning) zero)
          (P3.remainder (SU2.recursion bishopRunning) zero))
        (UV.embed 0ℚ)

    richAddIsBishopAdd :
      ∀ left right →
      Bishop._≃_
        (Rich.add rich left right)
        (Bishop._+_ left right)

    p3RemainderSameRichRegularPlusLiteralInteraction :
      ∀ depth →
      Bishop._≃_
        (P3.remainder (SU2.recursion bishopRunning) (suc depth))
        (Rich.add rich
          (Rich.regularRemainder rich depth)
          (UV.embed (Literal.literalBetaInt dataSet depth)))

    literalPlaquetteRepresentsCMP109 :
      LiteralToSource.LiteralPlaquetteCMP109UVSameObject dataSet trajectory

    traceBoundary :
      SU2.CanonicalBishopSU2TraceBoundary

open CanonicalS4RichProjectionMaxCut public

asCanonicalRichBridge :
  ∀ {trajectory split inputs rowA smallFieldCap largeFieldCap covarianceCap
      dataSet rich}
    (package : CanonicalS4RichProjectionMaxCut
      {trajectory = trajectory} {split = split}
      inputs rowA smallFieldCap largeFieldCap covarianceCap dataSet rich) →
  P3Rich.CanonicalRunningRichLiteralPlaquette
    dataSet rich (bishopRunning package)
asCanonicalRichBridge package = record
  { P3Rich.CanonicalRunningRichLiteralPlaquette.richNormalization =
      richNormalization package
  ; P3Rich.CanonicalRunningRichLiteralPlaquette.addIsBishopAdd =
      addIsBishopAdd package
  ; P3Rich.CanonicalRunningRichLiteralPlaquette.richAddIsBishopAdd =
      richAddIsBishopAdd package
  ; P3Rich.CanonicalRunningRichLiteralPlaquette.inverseCouplingSameLiteral =
      inverseCouplingSameLiteral package
  ; P3Rich.CanonicalRunningRichLiteralPlaquette.nextScaleIsUVPredecessor =
      nextScaleIsUVPredecessor package
  ; P3Rich.CanonicalRunningRichLiteralPlaquette.zeroTotalIncrementSame =
      zeroTotalIncrementSame package
  ; P3Rich.CanonicalRunningRichLiteralPlaquette.gaussianProjection =
      gaussianProjection package
  ; P3Rich.CanonicalRunningRichLiteralPlaquette.p3RemainderSameRichRegularPlusLiteralInteraction =
      p3RemainderSameRichRegularPlusLiteralInteraction package
  }

asP3LiteralTotal :
  ∀ {trajectory split inputs rowA smallFieldCap largeFieldCap covarianceCap
      dataSet rich}
    (package : CanonicalS4RichProjectionMaxCut
      {trajectory = trajectory} {split = split}
      inputs rowA smallFieldCap largeFieldCap covarianceCap dataSet rich) →
  P3Literal.P3RepresentsLiteralPlaquetteUVView
    dataSet (SU2.recursion (bishopRunning package))
asP3LiteralTotal package =
  P3Rich.canonicalRunningAsLiteralTotal (asCanonicalRichBridge package)

asCanonicalS4SameObjectPackage :
  ∀ {trajectory split inputs rowA smallFieldCap largeFieldCap covarianceCap
      dataSet rich}
    (package : CanonicalS4RichProjectionMaxCut
      {trajectory = trajectory} {split = split}
      inputs rowA smallFieldCap largeFieldCap covarianceCap dataSet rich) →
  S4.CanonicalS4SameObjectPackage
    {trajectory = trajectory} {split = split}
    inputs rowA smallFieldCap largeFieldCap covarianceCap
asCanonicalS4SameObjectPackage package = record
  { S4.CanonicalS4SameObjectPackage.betaCoordinates = betaCoordinates package
  ; S4.CanonicalS4SameObjectPackage.bishopRunning = bishopRunning package
  ; S4.CanonicalS4SameObjectPackage.bishopRunningRepresentsCMP109History =
      P3Literal.p3LiteralPlaquetteThenCMP109
        (asP3LiteralTotal package)
        (literalPlaquetteRepresentsCMP109 package)
  ; S4.CanonicalS4SameObjectPackage.traceBoundary = traceBoundary package
  }
normalizedLogCoordinateRequired : Bool
normalizedLogCoordinateRequired = false

independentP3RichGaussianWitnessRequired : Bool
independentP3RichGaussianWitnessRequired = false

independentP3LiteralGaussianWitnessRequired : Bool
independentP3LiteralGaussianWitnessRequired = false

p3RemainderIncludesRichRegularMatching : Bool
p3RemainderIncludesRichRegularMatching = true

richRationalGaussianProjectionRequired : Bool
richRationalGaussianProjectionRequired = true

normalizedLogCoordinateRequiredIsFalse :
  normalizedLogCoordinateRequired ≡ false
normalizedLogCoordinateRequiredIsFalse = refl

independentP3RichGaussianWitnessRequiredIsFalse :
  independentP3RichGaussianWitnessRequired ≡ false
independentP3RichGaussianWitnessRequiredIsFalse = refl

independentP3LiteralGaussianWitnessRequiredIsFalse :
  independentP3LiteralGaussianWitnessRequired ≡ false
independentP3LiteralGaussianWitnessRequiredIsFalse = refl

richRationalGaussianProjectionRequiredIsTrue :
  richRationalGaussianProjectionRequired ≡ true
richRationalGaussianProjectionRequiredIsTrue = refl

canonicalS4RichProjectionMaxCutCompilerLevel : ProofLevel
canonicalS4RichProjectionMaxCutCompilerLevel = machineChecked

canonicalS4RichProjectionPhysicalLevel : ProofLevel
canonicalS4RichProjectionPhysicalLevel = conditional
