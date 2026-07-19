module DASHI.Physics.QuantumVacuum.DiscriminatingExperiment where

------------------------------------------------------------------------
-- Generic control geometry for experiments whose observed signal admits
-- ordinary thermal, chemical, electromagnetic or instrumental explanations.
------------------------------------------------------------------------

record DiscriminatingExperiment
  (Signal NullHypothesis : Set) : Set₁ where
  constructor mkDiscriminatingExperiment
  field
    measuredSignal : Signal
    Control : NullHypothesis → Set
    controlReceipt : (h : NullHypothesis) → Control h
    exclusion : (h : NullHypothesis) → Control h → Set
    exclusionReceipt : (h : NullHypothesis) →
      exclusion h (controlReceipt h)

record ReplicatedDiscrimination
  (Signal NullHypothesis : Set) : Set₁ where
  constructor mkReplicatedDiscrimination
  field
    first second : DiscriminatingExperiment Signal NullHypothesis
    independentApparatus : Set
    independentAnalysis  : Set

replicationIncludesFirstExperiment :
  {Signal NullHypothesis : Set} →
  ReplicatedDiscrimination Signal NullHypothesis →
  DiscriminatingExperiment Signal NullHypothesis
replicationIncludesFirstExperiment r =
  ReplicatedDiscrimination.first r
