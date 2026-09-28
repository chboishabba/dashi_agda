{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCanonicalS4LocalPhysicalEdgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Rational.Base using (ℚ)

import Real as Bishop

import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact as SU2
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalRowABetaDrivenStateExact as RowAState
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalS4SameObjectPackageExact as S4
import DASHI.Physics.Foundations.CMP119AntigravityCMP109TrajectoryPlaquetteConstructorExact as Constructor
import DASHI.Physics.Foundations.CMP119AntigravityP3LiteralEdgeIncrementFromRichExact as Edge
import DASHI.Physics.Foundations.CMP119AntigravityP3LiteralPlaquetteRecurrenceSameObjectExact as Local
import DASHI.Physics.Foundations.CMP119AntigravityP3SourceRecurrenceUniquenessExact as Recurrence
import DASHI.Physics.Foundations.CMP119AntigravityP3StateForcesSourceIncrementExact as State
import DASHI.Physics.Foundations.CMP119AntigravitySourceHistoryBishopUVViewExact as UV
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaFlow
import DASHI.Physics.YangMills.BalabanClayP3PhysicalOneStepTransferExact as P3
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact as Split
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- PREFERRED S4 CUT AFTER POSITIVE-EDGE COMPILATION
--
-- The S4 caller no longer supplies
--
--   P3 total increment = literal beta
--
-- directly.  It supplies the strictly more physical local data:
--
--   * one UV state anchor;
--   * P3 addition / predecessor orientation;
--   * canonical rich one-loop normalization/projection;
--   * identification of the P3 remainder with the local regular+interaction
--     remainder on each positive edge.
--
-- `P3LiteralEdgeIncrementFromRichExact` then compiles the total edge increment,
-- and recurrence uniqueness reconstructs the complete P3/CMP109 history.
------------------------------------------------------------------------

record CanonicalS4LocalPhysicalEdgeInputs
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

    edgePhysics :
      Edge.CanonicalP3LiteralEdgeIncrementInputs
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

    sameUVAnchorAsLiteralNext :
      Bishop._≃_
        (P3.inverseCouplingSq (SU2.recursion bishopRunning) zero)
        (UV.embed
          (Plaquette.nextInverseCouplingSq
            (Constructor.asPhysicalRunningCouplingData coefficientWeld)
            zero))

    traceBoundary : SU2.CanonicalBishopSU2TraceBoundary

open CanonicalS4LocalPhysicalEdgeInputs public

asLocalP3LiteralRecurrence :
  ∀ {trajectory split inputs rowA smallFieldCap largeFieldCap covarianceCap}
    (package : CanonicalS4LocalPhysicalEdgeInputs
      {trajectory = trajectory} {split = split}
      inputs rowA smallFieldCap largeFieldCap covarianceCap) →
  Local.P3LiteralPlaquetteRecurrenceSameObject
    (Constructor.asPhysicalRunningCouplingData (coefficientWeld package))
    (SU2.recursion (bishopRunning package))
asLocalP3LiteralRecurrence package = record
  { Local.P3LiteralPlaquetteRecurrenceSameObject.addIsBishopAdd =
      p3AddIsBishopAdd package
  ; Local.P3LiteralPlaquetteRecurrenceSameObject.nextScaleIsUVPredecessor =
      p3NextScaleIsUVPredecessor package
  ; Local.P3LiteralPlaquetteRecurrenceSameObject.sameUVAnchorAsLiteralNext =
      sameUVAnchorAsLiteralNext package
  ; Local.P3LiteralPlaquetteRecurrenceSameObject.successorTotalIncrementSameLiteral =
      Edge.successorTotalIncrementSameLiteral (edgePhysics package)
  }

sourceRecurrenceSameObject :
  ∀ {trajectory split inputs rowA smallFieldCap largeFieldCap covarianceCap}
    (package : CanonicalS4LocalPhysicalEdgeInputs
      {trajectory = trajectory} {split = split}
      inputs rowA smallFieldCap largeFieldCap covarianceCap) →
  Recurrence.P3SourceRecurrenceSameObject
    trajectory
    (SU2.recursion (bishopRunning package))
sourceRecurrenceSameObject package =
  Local.asSourceRecurrenceSameObject
    (asLocalP3LiteralRecurrence package)
    (Constructor.asLiteralPlaquetteCMP109UVSameObject
      (coefficientWeld package))

asCanonicalS4SameObjectPackage :
  ∀ {trajectory split inputs rowA smallFieldCap largeFieldCap covarianceCap} →
  CanonicalS4LocalPhysicalEdgeInputs
    {trajectory = trajectory} {split = split}
    inputs rowA smallFieldCap largeFieldCap covarianceCap →
  S4.CanonicalS4SameObjectPackage
    {trajectory = trajectory} {split = split}
    inputs rowA smallFieldCap largeFieldCap covarianceCap
asCanonicalS4SameObjectPackage package = record
  { S4.CanonicalS4SameObjectPackage.betaCoordinates = betaCoordinates package
  ; S4.CanonicalS4SameObjectPackage.bishopRunning = bishopRunning package
  ; S4.CanonicalS4SameObjectPackage.bishopRunningRepresentsCMP109History =
      State.asP3RepresentsSourceUVView
        (Recurrence.asP3StateRepresentsSourceUV
          (sourceRecurrenceSameObject package))
  ; S4.CanonicalS4SameObjectPackage.traceBoundary = traceBoundary package
  }

directPositiveEdgeTotalIncrementWitnessRequired : Bool
directPositiveEdgeTotalIncrementWitnessRequired = false

allDepthP3StateWitnessRequired : Bool
allDepthP3StateWitnessRequired = false

sameUVAnchorStillRequired : Bool
sameUVAnchorStillRequired = true

localP3RemainderPhysicalIdentificationStillRequired : Bool
localP3RemainderPhysicalIdentificationStillRequired = true

directPositiveEdgeTotalIncrementWitnessRequiredIsFalse :
  directPositiveEdgeTotalIncrementWitnessRequired ≡ false
directPositiveEdgeTotalIncrementWitnessRequiredIsFalse = refl

allDepthP3StateWitnessRequiredIsFalse :
  allDepthP3StateWitnessRequired ≡ false
allDepthP3StateWitnessRequiredIsFalse = refl

canonicalS4LocalPhysicalEdgeCompilerLevel : ProofLevel
canonicalS4LocalPhysicalEdgeCompilerLevel = machineChecked
