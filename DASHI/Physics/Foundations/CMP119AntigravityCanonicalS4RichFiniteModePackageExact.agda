{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCanonicalS4RichFiniteModePackageExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; 0ℚ)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact as SU2
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopRichBrillouinUVEdgeExact as RichNorm
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalRowABetaDrivenStateExact as RowAState
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalS4SameObjectPackageExact as S4
import DASHI.Physics.Foundations.CMP119AntigravityCMP109TrajectoryPlaquetteConstructorExact as Constructor
import DASHI.Physics.Foundations.CMP119AntigravityFiniteModePlaquetteBetaSameObjectExact as FinitePlaquette
import DASHI.Physics.Foundations.CMP119AntigravityP3LiteralPlaquetteCMP109SameObjectExact as P3Literal
import DASHI.Physics.Foundations.CMP119AntigravityRichBrillouinFiniteModeGaussianProjectionExact as RichFinite
import DASHI.Physics.Foundations.CMP119AntigravityRichBrillouinRationalGaussianProjectionExact as Projection
import DASHI.Physics.Foundations.CMP119AntigravitySourceHistoryBishopUVViewExact as UV
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaFlow
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact as Split
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as FiniteMode
import DASHI.Physics.YangMills.BalabanYM4LiteralPlaquetteBetaEstimateExact as Literal
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanClayP3PhysicalOneStepTransferExact as P3
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- PREFERRED S4 PACKAGE THROUGH THE FINITE-MODE GAUSSIAN OWNER
--
-- A single RichBrillouinFiniteModeGaussianSameObject already contains the
-- componentwise finite-mode/plaqueette weld.  From it we derive:
--
--   rich shell -> rational plaquette beta_Z,
--   source beta -> literal plaquette total coefficient,
--   literal plaquette -> CMP109 UV history.
--
-- Thus neither gaussianProjection nor literalPlaquetteRepresentsCMP109 is an
-- independent caller input on this route.
------------------------------------------------------------------------

coefficientWeld :
  ∀ {trajectory Mode Atom finiteMode oneLoop remainder rich} →
  RichFinite.RichBrillouinFiniteModeGaussianSameObject
    {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
    finiteMode oneLoop remainder rich →
  Constructor.CMP109LiteralPlaquetteCoefficientWeld trajectory
coefficientWeld sameObject =
  FinitePlaquette.asCMP109LiteralPlaquetteCoefficientWeld
    (RichFinite.finiteModePlaquette sameObject)

dataSet :
  ∀ {trajectory Mode Atom finiteMode oneLoop remainder rich}
    (sameObject : RichFinite.RichBrillouinFiniteModeGaussianSameObject
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
      finiteMode oneLoop remainder rich) →
  Plaquette.PhysicalRunningCouplingData Nat
dataSet sameObject =
  Constructor.asPhysicalRunningCouplingData (coefficientWeld sameObject)

record CanonicalS4RichFiniteModeInputs
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {split : Split.FiniteLatticeBetaSplit trajectory}
    {Mode Atom : Set}
    {finiteMode : FiniteMode.FiniteModeBetaTrajectoryData trajectory Mode Atom}
    {oneLoop : Plaquette.OneLoopVacuumPolarizationData Nat}
    {remainder : Plaquette.PlaquetteRemainderData Nat}
    {rich : Rich.LiteralBrillouinIntegralPhysicalData Nat Bishop.ℝ}
    (sameObject : RichFinite.RichBrillouinFiniteModeGaussianSameObject
      finiteMode oneLoop remainder rich)
    (inputs : BetaFlow.BetaDrivenCompleteDensityInputs {trajectory} {split})
    (rowA : RowA.FiniteQuarticResponseConstants)
    (smallFieldCap largeFieldCap covarianceCap : ℚ) : Set₂ where
  field
    betaCoordinates :
      RowAState.CanonicalRowABetaDrivenCoordinates
        inputs rowA smallFieldCap largeFieldCap covarianceCap

    bishopRunning : SU2.CanonicalBishopSU2RunningInputs Nat

    richNormalization :
      RichNorm.CanonicalBishopRichBrillouinUVEdgeNormalization
        rich bishopRunning

    addIsBishopAdd :
      ∀ left right →
      Bishop._≃_
        (P3.add (SU2.recursion bishopRunning) left right)
        (Bishop._+_ left right)

    inverseCouplingSameLiteral :
      ∀ depth →
      Bishop._≃_
        (P3.inverseCouplingSq (SU2.recursion bishopRunning) depth)
        (UV.embed (Plaquette.inverseCouplingSq (dataSet sameObject) depth))

    nextScaleIsUVPredecessor :
      ∀ depth →
      P3.nextScale (SU2.recursion bishopRunning) depth ≡ UV.uvNext depth

    zeroTotalIncrementSame :
      Bishop._≃_
        (Bishop._+_
          (P3.betaLogBlocking (SU2.recursion bishopRunning) zero)
          (P3.remainder (SU2.recursion bishopRunning) zero))
        (UV.embed 0ℚ)

    remainderSameLiteralInteraction :
      ∀ depth →
      Bishop._≃_
        (P3.remainder (SU2.recursion bishopRunning) (suc depth))
        (UV.embed (Literal.literalBetaInt (dataSet sameObject) depth))

    traceBoundary : SU2.CanonicalBishopSU2TraceBoundary

open CanonicalS4RichFiniteModeInputs public

gaussianProjection :
  ∀ {trajectory split Mode Atom finiteMode oneLoop remainder rich
      sameObject inputs rowA smallFieldCap largeFieldCap covarianceCap} →
  CanonicalS4RichFiniteModeInputs
    {trajectory = trajectory} {split = split}
    {Mode = Mode} {Atom = Atom}
    {finiteMode = finiteMode} {oneLoop = oneLoop}
    {remainder = remainder} {rich = rich}
    sameObject inputs rowA smallFieldCap largeFieldCap covarianceCap →
  Projection.RichBrillouinRationalGaussianProjection
    (dataSet sameObject) rich
gaussianProjection {sameObject = sameObject} package =
  RichFinite.asRichBrillouinRationalGaussianProjection sameObject

asP3LiteralSplit :
  ∀ {trajectory split Mode Atom finiteMode oneLoop remainder rich
      sameObject inputs rowA smallFieldCap largeFieldCap covarianceCap}
    (package : CanonicalS4RichFiniteModeInputs
      {trajectory = trajectory} {split = split}
      {Mode = Mode} {Atom = Atom}
      {finiteMode = finiteMode} {oneLoop = oneLoop}
      {remainder = remainder} {rich = rich}
      sameObject inputs rowA smallFieldCap largeFieldCap covarianceCap) →
  P3Literal.P3RepresentsLiteralPlaquetteSplitUVView
    (dataSet sameObject) (SU2.recursion (bishopRunning package))
asP3LiteralSplit {sameObject = sameObject} package = record
  { P3Literal.P3RepresentsLiteralPlaquetteSplitUVView.addIsBishopAdd =
      addIsBishopAdd package
  ; P3Literal.P3RepresentsLiteralPlaquetteSplitUVView.inverseCouplingSameLiteral =
      inverseCouplingSameLiteral package
  ; P3Literal.P3RepresentsLiteralPlaquetteSplitUVView.nextScaleIsUVPredecessor =
      nextScaleIsUVPredecessor package
  ; P3Literal.P3RepresentsLiteralPlaquetteSplitUVView.zeroTotalIncrementSame =
      zeroTotalIncrementSame package
  ; P3Literal.P3RepresentsLiteralPlaquetteSplitUVView.betaLogBlockingSameLiteralGaussian =
      λ depth →
        BishopP.≃-trans
          (RichNorm.p3SuccessorGaussianSameRichEdgeIntegral
            (richNormalization package) depth)
          (Projection.scalarIntegralSameLiteralGaussian
            (RichFinite.asRichBrillouinRationalGaussianProjection sameObject)
            depth)
  ; P3Literal.P3RepresentsLiteralPlaquetteSplitUVView.remainderSameLiteralInteraction =
      remainderSameLiteralInteraction package
  }

asCanonicalS4SameObjectPackage :
  ∀ {trajectory split Mode Atom finiteMode oneLoop remainder rich
      sameObject inputs rowA smallFieldCap largeFieldCap covarianceCap}
    (package : CanonicalS4RichFiniteModeInputs
      {trajectory = trajectory} {split = split}
      {Mode = Mode} {Atom = Atom}
      {finiteMode = finiteMode} {oneLoop = oneLoop}
      {remainder = remainder} {rich = rich}
      sameObject inputs rowA smallFieldCap largeFieldCap covarianceCap) →
  S4.CanonicalS4SameObjectPackage
    {trajectory = trajectory} {split = split}
    inputs rowA smallFieldCap largeFieldCap covarianceCap
asCanonicalS4SameObjectPackage {sameObject = sameObject} package = record
  { S4.CanonicalS4SameObjectPackage.betaCoordinates = betaCoordinates package
  ; S4.CanonicalS4SameObjectPackage.bishopRunning = bishopRunning package
  ; S4.CanonicalS4SameObjectPackage.bishopRunningRepresentsCMP109History =
      P3Literal.p3LiteralPlaquetteThenCMP109
        (P3Literal.splitViewAsTotalView (asP3LiteralSplit package))
        (Constructor.asLiteralPlaquetteCMP109UVSameObject
          (coefficientWeld sameObject))
  ; S4.CanonicalS4SameObjectPackage.traceBoundary = traceBoundary package
  }

independentGaussianProjectionRequired : Agda.Builtin.Bool.Bool
independentGaussianProjectionRequired = Agda.Builtin.Bool.false

independentLiteralCMP109WeldRequired : Agda.Builtin.Bool.Bool
independentLiteralCMP109WeldRequired = Agda.Builtin.Bool.false

canonicalS4RichFiniteModeCompilerLevel : ProofLevel
canonicalS4RichFiniteModeCompilerLevel = machineChecked

richShellFiniteModeGaussianPhysicalIdentificationLevel : ProofLevel
richShellFiniteModeGaussianPhysicalIdentificationLevel = conditional
