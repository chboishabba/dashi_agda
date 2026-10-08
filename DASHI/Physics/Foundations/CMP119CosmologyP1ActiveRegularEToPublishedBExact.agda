{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP1ActiveRegularEToPublishedBExact where

open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Physics.Foundations.CMP119CosmologyP1SourceFirstPublishedBContinuationExact as PublishedB
import DASHI.Physics.YangMills.BalabanCMP119RegularESection2PredicateRound246Exact as R246
import DASHI.Physics.YangMills.BalabanTheorem1RegularEContinuationRound247Exact as R247
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as FiniteBeta
import DASHI.Physics.YangMills.Balaban1989FiniteModeInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- S1 SOURCE PAYMENT AFTER THE PUBLISHED-B RECUT.
--
-- Round247 already shows that the CMP109/116 continuation consumes only the
-- active regular-E/localization form witness, not the independent quantitative
-- part of the full CMP122 Theorem-1 package.  This adapter presents exactly that
-- witness in the newer source-first carrier:
--
--   PublishedB := the SAME Background carrier of the active Section-2 source;
--   Scale      := the SAME active finite-beta-history scale fibre;
--   Tangent    := chosen later, definitionally, as the ten-slot symmetric
--                 metric/source carrier by SourceFirstPublishedBContinuation.
--
-- Hence no post-hoc Background equality, tangent equality, or second localized
-- finite-sum theorem is charged.  The remaining physical/source payment is the
-- literal active regular-E form witness on the selected CMP119 source family.
------------------------------------------------------------------------

activeRegularEFormAsPublishedBContinuation :
  ∀ {trajectory Mode Atom betaData history}
    {dataSet : R246.ActiveRegularESection2Inputs
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
      betaData history} →
  R246.ActiveRegularESection2FormWitness dataSet →
  PublishedB.SourceFirstPublishedBContinuation
    (R247.ActiveScaleIndex history)
    (R246.ActiveRegularESection2Inputs.Volume dataSet)
    (R246.ActiveRegularESection2Inputs.Background dataSet)
    (R246.ActiveRegularESection2Inputs.Component dataSet)
activeRegularEFormAsPublishedBContinuation
    {history = history} {dataSet = dataSet} formWitness = record
  { PublishedB.SourceFirstPublishedBContinuation.components =
      λ index volume →
        R246.components
          (R246.regularEFormOnActiveScale formWitness
            (R247.scale index) (R247.active index))
          volume
  ; PublishedB.SourceFirstPublishedBContinuation.cmp116PhysicalLocalizedActivity =
      λ index volume component →
        R246.localizedRegularActivity
          (R246.regularEFormOnActiveScale formWitness
            (R247.scale index) (R247.active index))
          volume component
  ; PublishedB.SourceFirstPublishedBContinuation.cmp109EffectivePotential =
      λ index _ →
        R246.regularE
          (R246.regularEFormOnActiveScale formWitness
            (R247.scale index) (R247.active index))
  ; PublishedB.SourceFirstPublishedBContinuation.effectivePotentialIsLocalizedCompositeSum =
      λ index volume →
        R246.regularEIsLocalizedCompositeSum
          (R246.regularEFormOnActiveScale formWitness
            (R247.scale index) (R247.active index))
          volume
  }

activeRegularEFormToPublishedBContinuationCompilerLevel : ProofLevel
activeRegularEFormToPublishedBContinuationCompilerLevel = machineChecked

activeRegularEFormToPublishedBContinuationCompilerClosed : Bool
activeRegularEFormToPublishedBContinuationCompilerClosed = true

fullTheorem1QuantitativePackageRequiredForS1 : Bool
fullTheorem1QuantitativePackageRequiredForS1 = false

literalActiveRegularEFormOnPublishedBStillRequired : Bool
literalActiveRegularEFormOnPublishedBStillRequired = true

-- This is exactly the source-level conditional already isolated by Round247.
literalActiveRegularEFormOnPublishedBLevel : ProofLevel
literalActiveRegularEFormOnPublishedBLevel =
  R247.literalActiveCMP119RegularESection2FormWitnessLevel
