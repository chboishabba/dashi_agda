module DASHI.Reasoning.DustReferenceStepContractExact where

-- Dust reference: qlabs-eng/dust dust.py, Git blob
-- c7d08ee9edc3a51dfbd9e73bbf787b9ca819c5c2, fetched 2026-10-26.
-- Original algorithm authors: Samip Dahal, Bishwas Mandal,
-- Serdar Gülbahar, Akshay Vegesna.
-- DASHI source-refinement specification only; no fresh kernel receipt.
--
-- This module does not import or modify LILA. The future LILA worker may
-- consume the transition and supply actual task and held-out receipts.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

data DustParameterKind : Set where
  writer : DustParameterKind
  mlpHidden : DustParameterKind
  tokenEmbedding : DustParameterKind
  attentionHub : DustParameterKind
  cachedLogitHead : DustParameterKind
  localQuery : DustParameterKind
  localKey : DustParameterKind
  localValue : DustParameterKind
  localGate : DustParameterKind
  localValueEmbedding : DustParameterKind
  residualLambda : DustParameterKind
  x0Lambda : DustParameterKind

data DustEstimatorRoute : Set where
  directChunkLoss : DustEstimatorRoute
  localAttentionOutput : DustEstimatorRoute
  cachedHeadSlab : DustEstimatorRoute
  twoSidedScalarES : DustEstimatorRoute

referenceRoute : DustParameterKind → DustEstimatorRoute
referenceRoute writer = directChunkLoss
referenceRoute mlpHidden = directChunkLoss
referenceRoute tokenEmbedding = directChunkLoss
referenceRoute attentionHub = directChunkLoss
referenceRoute cachedLogitHead = cachedHeadSlab
referenceRoute localQuery = localAttentionOutput
referenceRoute localKey = localAttentionOutput
referenceRoute localValue = localAttentionOutput
referenceRoute localGate = localAttentionOutput
referenceRoute localValueEmbedding = localAttentionOutput
referenceRoute residualLambda = twoSidedScalarES
referenceRoute x0Lambda = twoSidedScalarES

referenceRouteIsLiteral :
  (k : DustParameterKind) → referenceRoute k ≡ referenceRoute k
referenceRouteIsLiteral _ = refl

-- This distinction is specific to upstream direct_errors:
-- if nrep > 1, center clean-minus-noisy loss within each draw chunk;
-- nrep=1 does not center.
record DirectChunkContract : Set where
  field
    chunkDraws : Nat
    rewardCentered : Bool
    chunkPopulationWellFormed : Bool
    sigmaNonzero : Bool
    sourceGitBlob : String

-- A separate optimizer interface does not smuggle Adam into Dust's
-- reference SGD-with-momentum step. Per-parameter learning-rate groups
-- include wte=1000, value_embeds=0.3, lambdas=0.03; remaining use recipe lr.
record SourceStep (Parameter Gradient Momentum Scalar : Set) : Set₁ where
  field
    parametersBefore : Parameter
    measuredGradient : Gradient
    momentumBefore momentumAfter : Momentum
    parametersAfter : Parameter
    updateByMomentumSGD : Parameter → Gradient → Momentum → Parameter
    updateLaw : parametersAfter ≡
      updateByMomentumSGD parametersBefore measuredGradient momentumAfter
    noReverseADClaim : Bool
    sourceGitBlob : String

-- This law is a real compositional consumer statement, but
-- no source-to-formal equivalence follows without implementations
-- of reassembly, rank-averaging and momentum SGD.
referenceTransitionByContract :
  {P G M S : Set} (step : SourceStep P G M S) →
  SourceStep.parametersAfter step ≡
    SourceStep.updateByMomentumSGD step
      (SourceStep.parametersBefore step)
      (SourceStep.measuredGradient step)
      (SourceStep.momentumAfter step)
referenceTransitionByContract step = SourceStep.updateLaw step

-- LILA handoff: an independent worker supplies a parameter mapping and
-- held-out semantic pair evaluator; this owner must not guess their types.
record LILAHandoff (Parameter Task Pair Metric : Set) : Set₁ where
  field
    task : Task
    initial final : Parameter
    evaluatePair : Parameter → Pair → Metric
    beforeAfterObservation : Pair → Metric → Metric
    sourceOwner : String
    heldOutDatasetIdentity : String
