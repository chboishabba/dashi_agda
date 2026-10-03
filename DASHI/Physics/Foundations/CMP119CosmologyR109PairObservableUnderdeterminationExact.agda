{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyR109PairObservableUnderdeterminationExact where

------------------------------------------------------------------------
-- E2/E4 MAX-CUT: THE ROUND109 SOURCE PAIR DOES NOT ITSELF CARRY AN OBSERVABLE.
--
-- `SourceNativeOrdinaryCharacteristicPair` contains only a source-native pair
-- token plus its local-analytic admissibility proof.  In particular, its type
-- has no eliminator into a selected configuration-space real observable.
--
-- The current functional presentation is therefore correctly cut at ONE
-- semantic evaluator
--
--   pair -> Configuration -> R.
--
-- This file makes the non-uniqueness precise.  If two candidate evaluators
-- disagree on the selected stress pair at one configuration, then no theorem
-- can identify both candidate presentations pointwise.  Hence the E2/E4 leaf
-- is genuinely the source-semantics evaluator (or an equivalent published
-- same-object theorem), not another OS positivity or clustering estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.YangMills.BalabanCMP119CompatibleLocalExpectationFlowExact as Source
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109

record PairObservableDisagreement
    (source : R109.SourceNativeStressScaleCauchy)
    (Configuration : Set) : Set₁ where
  field
    leftEvaluator :
      Source.SourceNativeOrdinaryCharacteristicPair (R109.source source) →
      Configuration → ℝ

    rightEvaluator :
      Source.SourceNativeOrdinaryCharacteristicPair (R109.source source) →
      Configuration → ℝ

    witnessConfiguration : Configuration

    selectedStressDisagrees :
      leftEvaluator (R109.stressInsertion source) witnessConfiguration
      ≡
      rightEvaluator (R109.stressInsertion source) witnessConfiguration
      →
      ⊥

open PairObservableDisagreement public

noPointwiseUniquenessFromBarePair :
  ∀ {source Configuration}
    (disagreement : PairObservableDisagreement source Configuration) →
  (∀ configuration →
    leftEvaluator disagreement (R109.stressInsertion source) configuration
    ≡
    rightEvaluator disagreement (R109.stressInsertion source) configuration) →
  ⊥
noPointwiseUniquenessFromBarePair disagreement pointwise =
  selectedStressDisagrees disagreement
    (pointwise (witnessConfiguration disagreement))

r109PairCarrierContainsSelectedObservableEvaluator : Bool
r109PairCarrierContainsSelectedObservableEvaluator = false

remainingE2E4LeafIsSourceSemanticsEvaluator : Bool
remainingE2E4LeafIsSourceSemanticsEvaluator = true

e2GramPositivityIsIndependentRemainingLeaf : Bool
e2GramPositivityIsIndependentRemainingLeaf = false

e4ClusteringEstimateIsIndependentRemainingLeaf : Bool
e4ClusteringEstimateIsIndependentRemainingLeaf = false
