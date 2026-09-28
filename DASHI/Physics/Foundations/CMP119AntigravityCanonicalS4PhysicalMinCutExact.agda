{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCanonicalS4PhysicalMinCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (ℚ)

import Real as Bishop

import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact as SU2
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalRowABetaDrivenStateExact as RowAState
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalS4LocalPhysicalEdgeExact as LocalS4
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalS4SameObjectPackageExact as S4
import DASHI.Physics.Foundations.CMP119AntigravityCMP109TrajectoryPlaquetteConstructorExact as Constructor
import DASHI.Physics.Foundations.CMP119AntigravityP3LiteralEdgeIncrementMinCutExact as Edge
import DASHI.Physics.Foundations.CMP119AntigravityP3UVAnchorFromSharedCouplingExact as UVAnchor
import DASHI.Physics.Foundations.CMP119AntigravityP3GPhysicalProducerMinCutExact as P3G
import DASHI.Physics.Foundations.CMP119AntigravitySourceHistoryBishopUVViewExact as UV
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaFlow
import DASHI.Physics.YangMills.BalabanClayP3PhysicalOneStepTransferExact as P3
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact as Split
import DASHI.Physics.YangMills.BalabanYM4LiteralPlaquetteBetaEstimateExact as Literal
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- ANTIGRAVITY S4 PHYSICAL MIN-CUT
--
-- All all-depth/history equalities and all total-increment equalities have
-- already been compiled away.  With the canonical Row-A, literal/CMP109 and
-- rich one-loop geometry fixed, the physical P3 payments are exactly:
--
--   A. initial inverseCouplingSq uses the SAME beta-history coupling g_0;
--   B. P3 positive-edge remainder is the SAME local regular+interaction
--      remainder.
--
-- Everything else below is structural carrier/orientation data or already-owned
-- same-object geometry.
------------------------------------------------------------------------

record CanonicalS4PhysicalMinCut
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {split : Split.FiniteLatticeBetaSplit trajectory}
    (inputs : BetaFlow.BetaDrivenCompleteDensityInputs {trajectory} {split})
    (rowA : RowA.FiniteQuarticResponseConstants)
    (smallFieldCap largeFieldCap covarianceCap : ℚ) : Set₂ where
  field
    betaCoordinates :
      RowAState.CanonicalRowABetaDrivenCoordinates
        inputs rowA smallFieldCap largeFieldCap covarianceCap

    bishopRunning : SU2.CanonicalBishopSU2RunningInputs Nat

    coefficientWeld :
      Constructor.CMP109LiteralPlaquetteCoefficientWeld trajectory

    rich : Rich.LiteralBrillouinIntegralPhysicalData Nat Bishop.ℝ

    edgeGeometry :
      Edge.CanonicalP3LiteralEdgeGeometry
        (Constructor.asPhysicalRunningCouplingData coefficientWeld)
        rich
        bishopRunning

    p3AddIsBishopAdd :
      ∀ left right →
      Bishop._≃_
        (P3.add (SU2.recursion bishopRunning) left right)
        (Bishop._+_ left right)

    p3NextScaleIsUVPredecessor :
      ∀ depth →
      P3.nextScale (SU2.recursion bishopRunning) depth ≡ UV.uvNext depth

    p3GPhysicalProducer :
      P3G.P3GPhysicalProducerMinCut
        (BetaFlow.betaHistory inputs)
        (Constructor.asPhysicalRunningCouplingData coefficientWeld)
        rich
        bishopRunning
        edgeGeometry

    traceBoundary : SU2.CanonicalBishopSU2TraceBoundary

open CanonicalS4PhysicalMinCut public

asLocalS4Inputs :
  ∀ {trajectory split inputs rowA smallFieldCap largeFieldCap covarianceCap} →
  CanonicalS4PhysicalMinCut
    {trajectory = trajectory} {split = split}
    inputs rowA smallFieldCap largeFieldCap covarianceCap →
  LocalS4.CanonicalS4LocalPhysicalEdgeInputs
    {trajectory = trajectory} {split = split}
    inputs rowA smallFieldCap largeFieldCap covarianceCap
asLocalS4Inputs package = record
  { LocalS4.CanonicalS4LocalPhysicalEdgeInputs.betaCoordinates =
      betaCoordinates package
  ; LocalS4.CanonicalS4LocalPhysicalEdgeInputs.bishopRunning =
      bishopRunning package
  ; LocalS4.CanonicalS4LocalPhysicalEdgeInputs.coefficientWeld =
      coefficientWeld package
  ; LocalS4.CanonicalS4LocalPhysicalEdgeInputs.rich =
      rich package
  ; LocalS4.CanonicalS4LocalPhysicalEdgeInputs.edgeGeometry =
      edgeGeometry package
  ; LocalS4.CanonicalS4LocalPhysicalEdgeInputs.p3RemainderIsLocalPhysicalRemainder =
      P3G.positiveEdgeRemainderIsPhysical (p3GPhysicalProducer package)
  ; LocalS4.CanonicalS4LocalPhysicalEdgeInputs.p3AddIsBishopAdd =
      p3AddIsBishopAdd package
  ; LocalS4.CanonicalS4LocalPhysicalEdgeInputs.p3NextScaleIsUVPredecessor =
      p3NextScaleIsUVPredecessor package
  ; LocalS4.CanonicalS4LocalPhysicalEdgeInputs.p3InitialInverseSquareUsesHistoryCoupling =
      P3G.initialInverseSquareUsesSameCoupling (p3GPhysicalProducer package)
  ; LocalS4.CanonicalS4LocalPhysicalEdgeInputs.traceBoundary =
      traceBoundary package
  }

asCanonicalS4SameObjectPackage :
  ∀ {trajectory split inputs rowA smallFieldCap largeFieldCap covarianceCap} →
  CanonicalS4PhysicalMinCut
    {trajectory = trajectory} {split = split}
    inputs rowA smallFieldCap largeFieldCap covarianceCap →
  S4.CanonicalS4SameObjectPackage
    {trajectory = trajectory} {split = split}
    inputs rowA smallFieldCap largeFieldCap covarianceCap
asCanonicalS4SameObjectPackage package =
  LocalS4.asCanonicalS4SameObjectPackage (asLocalS4Inputs package)

directUVStateAnchorPaymentRequired : Bool
directUVStateAnchorPaymentRequired = false

directPositiveEdgeIncrementPaymentRequired : Bool
directPositiveEdgeIncrementPaymentRequired = false

allDepthStateHistoryPaymentRequired : Bool
allDepthStateHistoryPaymentRequired = false

initialSharedCouplingRepresentationPaymentRequired : Bool
initialSharedCouplingRepresentationPaymentRequired = true

localP3RemainderProducerPaymentRequired : Bool
localP3RemainderProducerPaymentRequired = true

directUVStateAnchorPaymentRequiredIsFalse :
  directUVStateAnchorPaymentRequired ≡ false
directUVStateAnchorPaymentRequiredIsFalse = refl

directPositiveEdgeIncrementPaymentRequiredIsFalse :
  directPositiveEdgeIncrementPaymentRequired ≡ false
directPositiveEdgeIncrementPaymentRequiredIsFalse = refl

allDepthStateHistoryPaymentRequiredIsFalse :
  allDepthStateHistoryPaymentRequired ≡ false
allDepthStateHistoryPaymentRequiredIsFalse = refl

initialSharedCouplingRepresentationPaymentRequiredIsTrue :
  initialSharedCouplingRepresentationPaymentRequired ≡ true
initialSharedCouplingRepresentationPaymentRequiredIsTrue = refl

localP3RemainderProducerPaymentRequiredIsTrue :
  localP3RemainderProducerPaymentRequired ≡ true
localP3RemainderProducerPaymentRequiredIsTrue = refl

canonicalS4PhysicalMinCutCompilerLevel : ProofLevel
canonicalS4PhysicalMinCutCompilerLevel = machineChecked

p3InitialSharedCouplingRepresentationLevel : ProofLevel
p3InitialSharedCouplingRepresentationLevel = conditional

p3LocalRemainderProducerLevel : ProofLevel
p3LocalRemainderProducerLevel = conditional
