module DASHI.Governance.WeightedEpistemicPipelineExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Weighted epistemic-pipeline algebra.
--
-- A possible transition is not automatically a high-gain transition.  We keep
-- weights abstract so that empirical probabilities, recommender scores, odds,
-- or qualitative orders may be supplied by a case-specific producer without
-- pretending that the generic carrier itself estimates them.
------------------------------------------------------------------------

record WeightedPipeline : Set₁ where
  field
    Node : Set
    Weight : Set
    Edge : Node → Node → Set
    edgeWeight :
      {x y : Node} →
      Edge x y → Weight
    AtLeast : Weight → Weight → Set

open WeightedPipeline public

record PossibleStep
  (P : WeightedPipeline)
  (x y : Node P) : Set where
  field
    edge : Edge P x y

open PossibleStep public

record ThresholdStep
  (P : WeightedPipeline)
  (threshold : Weight P)
  (x y : Node P) : Set where
  field
    edge : Edge P x y
    meetsThreshold :
      AtLeast P (edgeWeight P edge) threshold

open ThresholdStep public

thresholdStepIsPossible :
  ∀ {P : WeightedPipeline}
    {threshold : Weight P}
    {x y : Node P} →
  ThresholdStep P threshold x y →
  PossibleStep P x y
thresholdStepIsPossible step =
  record { edge = ThresholdStep.edge step }

------------------------------------------------------------------------
-- A path records local transition evidence.  No multiplication or Markov
-- interpretation is imported until a weight algebra is explicitly supplied.
------------------------------------------------------------------------

record TwoStepPath
  (P : WeightedPipeline)
  (x y z : Node P) : Set where
  field
    first : Edge P x y
    second : Edge P y z

record WeightedPathAlgebra
  (P : WeightedPipeline) : Set₁ where
  field
    combine : Weight P → Weight P → Weight P
    pathWeight :
      {x y z : Node P} →
      TwoStepPath P x y z →
      Weight P
    pathWeightEquation :
      {x y z : Node P} →
      (path : TwoStepPath P x y z) →
      pathWeight path
      ≡ combine
          (edgeWeight P (TwoStepPath.first path))
          (edgeWeight P (TwoStepPath.second path))

------------------------------------------------------------------------
-- Bridge nodes are graph-theoretic objects, not ideological classifications.
------------------------------------------------------------------------

record BridgeWitness
  (P : WeightedPipeline)
  (entry bridge exit : Node P) : Set where
  field
    intoBridge : Edge P entry bridge
    outOfBridge : Edge P bridge exit

record WeightedPipelineBoundary : Set where
  constructor weightedPipelineBoundary
  field
    possibleMeansHighProbability : Bool
    highThresholdStepRequiresPossibleEdge : Bool
    genericWeightEqualsProbability : Bool
    bridgeNodeImpliesExtremistIdentity : Bool
    calibratedProbabilityRequiresExternalEvidence : Bool

canonicalWeightedPipelineBoundary : WeightedPipelineBoundary
canonicalWeightedPipelineBoundary =
  weightedPipelineBoundary false true false false true
