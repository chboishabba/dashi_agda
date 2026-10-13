module DASHI.Biology.IIT4SystemPhiInputExact where

open import DASHI.Core.Prelude

import DASHI.Biology.IIT4FiniteCausalStructureExact as IIT4
import DASHI.Biology.IIT4FiniteProbabilityRepertoireExact as Prob

------------------------------------------------------------------------
-- IIT 4.0 SYSTEM-PHI INPUT SPINE
--
-- Albantakis et al. IIT 4.0 equations 19--23 use directional partitions,
-- compare unpartitioned and partitioned probabilities on cause/effect sides,
-- multiply the positive logarithmic ratio by a selectivity probability, take
-- the minimum of cause/effect irreducibility, and choose a normalized minimum
-- partition.
--
-- The directional partition object is owned once, in the finite causal core.
-- This module makes the scalar inputs and MIP obligation explicit without
-- rebuilding that partition vocabulary.
------------------------------------------------------------------------

-- Input data for equations of the form
--   p * | log (p / p_partitioned) |_+.
record ProbabilityLossInput : Set where
  constructor probabilityLossInput
  field
    selectivityWeight : Prob.ProbabilityFraction
    unpartitionedConditional : Prob.ProbabilityFraction
    partitionedConditional : Prob.ProbabilityFraction
    probabilityRole : String

open ProbabilityLossInput public

record IntrinsicInformationScalarBackend : Set₁ where
  constructor intrinsicInformationScalarBackend
  field
    Score : Set
    positiveLogRatio :
      Prob.ProbabilityFraction →
      Prob.ProbabilityFraction →
      Score
    weightByProbability : Prob.ProbabilityFraction → Score → Score
    minimumScore : Score → Score → Score
    normalizedPartitionScore : Score → Nat → Score
    scoreOrder : Score → Score → Set
    analyticReceipt : String

open IntrinsicInformationScalarBackend public

integratedSideScore :
  (backend : IntrinsicInformationScalarBackend) →
  ProbabilityLossInput → Score backend
integratedSideScore backend input =
  weightByProbability backend
    (selectivityWeight input)
    (positiveLogRatio backend
      (unpartitionedConditional input)
      (partitionedConditional input))

record CauseEffectPartitionInput
    (system : IIT4.FiniteCausalSystem) : Set where
  constructor causeEffectPartitionInput
  field
    directedCut : IIT4.SystemPartition system
    causeLoss : ProbabilityLossInput
    effectLoss : ProbabilityLossInput
    specifiedCauseState : IIT4.StateOf system
    specifiedEffectState : IIT4.StateOf system
    specifiedStateSelectionReceipt : String

open CauseEffectPartitionInput public

systemPhiAtPartition :
  (backend : IntrinsicInformationScalarBackend) →
  ∀ {system : IIT4.FiniteCausalSystem} →
  CauseEffectPartitionInput system → Score backend
systemPhiAtPartition backend input =
  minimumScore backend
    (integratedSideScore backend (causeLoss input))
    (integratedSideScore backend (effectLoss input))

normalizedSystemPhiAtPartition :
  (backend : IntrinsicInformationScalarBackend) →
  ∀ {system : IIT4.FiniteCausalSystem} →
  CauseEffectPartitionInput system → Score backend
normalizedSystemPhiAtPartition backend input =
  normalizedPartitionScore backend
    (systemPhiAtPartition backend input)
    (IIT4.affectedConnectionCount (directedCut input))

record MinimumPartitionWitness
    (backend : IntrinsicInformationScalarBackend)
    {system : IIT4.FiniteCausalSystem}
    (candidate : CauseEffectPartitionInput system)
    (alternatives : List (CauseEffectPartitionInput system)) : Set₁ where
  constructor minimumPartitionWitness
  field
    normalizedMinimalAgainst :
      (other : CauseEffectPartitionInput system) →
      IIT4._ListedIn_ other alternatives →
      scoreOrder backend
        (normalizedSystemPhiAtPartition backend candidate)
        (normalizedSystemPhiAtPartition backend other)
    tieBreakReceipt : String

open MinimumPartitionWitness public

record SystemPhiEvaluation
    (backend : IntrinsicInformationScalarBackend)
    (system : IIT4.FiniteCausalSystem) : Set₁ where
  constructor systemPhiEvaluation
  field
    candidatePartitions : List (CauseEffectPartitionInput system)
    minimumPartition : CauseEffectPartitionInput system
    minimumWitness :
      MinimumPartitionWitness
        backend minimumPartition candidatePartitions
    unnormalizedPhiS : Score backend
    scoreReceipt :
      unnormalizedPhiS ≡
      systemPhiAtPartition backend minimumPartition

open SystemPhiEvaluation public

------------------------------------------------------------------------
-- Normalization ownership.
-- IIT 4.0 uses the maximum possible number of affected pairwise interactions
-- for a partition as the normalization factor.  We retain that count as an
-- explicit field on the canonical partition, not as the final unnormalised
-- phi_s value.
------------------------------------------------------------------------

record PartitionNormalizationReceipt
    {system : IIT4.FiniteCausalSystem}
    (partition : IIT4.SystemPartition system) : Set where
  constructor partitionNormalizationReceipt
  field
    computedAffectedConnectionCount : Nat
    countMatchesPartition :
      computedAffectedConnectionCount ≡
      IIT4.affectedConnectionCount partition
    normalizationIsNotUnnormalizedPhi : Bool

open PartitionNormalizationReceipt public

record IIT4SystemPhiBoundary : Set where
  constructor iit4SystemPhiBoundary
  field
    reusesCanonicalDirectionalPartition : Bool
    causeAndEffectLossesRemainSeparate : Bool
    systemPhiAtCutIsMinimumCauseEffect : Bool
    MIPUsesNormalizedComparison : Bool
    returnedSystemPhiIsUnnormalizedAtMIP : Bool
    affectedConnectionCountEqualsReturnedPhiByDefinition : Bool
    finiteCountsImplementAnalyticLogByDefinition : Bool
    scoreOrderingRequiresDeclaredBackend : Bool

open IIT4SystemPhiBoundary public

canonicalIIT4SystemPhiBoundary : IIT4SystemPhiBoundary
canonicalIIT4SystemPhiBoundary =
  iit4SystemPhiBoundary
    true true true true true
    false false true

normalizerIsNotPhiByDefinition :
  affectedConnectionCountEqualsReturnedPhiByDefinition
    canonicalIIT4SystemPhiBoundary ≡ false
normalizerIsNotPhiByDefinition = refl

logRemainsAnalyticBackendObligation :
  finiteCountsImplementAnalyticLogByDefinition
    canonicalIIT4SystemPhiBoundary ≡ false
logRemainsAnalyticBackendObligation = refl
