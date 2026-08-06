module DASHI.Physics.YangMills.BalabanClayDenseCoreSpectralGapExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions", Communications in Mathematical
-- Physics 31 (1973), 83--112. DOI: 10.1007/BF01645738.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions II", Communications in
-- Mathematical Physics 42 (1975), 281--305. DOI: 10.1007/BF01608978.
--
-- DASHI CONTRIBUTION
--
-- The Clay-critical implication does not require one chosen observable to
-- overlap the lightest state.  It is enough that exponential clustering kills
-- the positive subgap spectral projection on a dense centered local core and
-- that the projection is continuous.  Density then kills the projection on
-- the whole vacuum-orthogonal Hilbert space.  Edge detection is deliberately
-- separated into another module.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record DenseCoreProjectionData
    (CoreVector HilbertVector : Set) : Set₁ where
  field
    includeCore : CoreVector → HilbertVector
    zeroVector : HilbertVector
    positiveSubgapProjection : HilbertVector → HilbertVector

    CoreClusteringEstimate : CoreVector → Set
    clusteringKillsSubgapProjection : ∀ core →
      CoreClusteringEstimate core →
      positiveSubgapProjection (includeCore core) ≡ zeroVector

    denseContinuousExtension :
      (∀ core →
        positiveSubgapProjection (includeCore core) ≡ zeroVector) →
      ∀ vector → positiveSubgapProjection vector ≡ zeroVector

open DenseCoreProjectionData public

record UniformDenseCoreClustering
    {CoreVector HilbertVector : Set}
    (dataSet : DenseCoreProjectionData CoreVector HilbertVector) : Set₁ where
  field
    clusteringOnEveryCoreVector : ∀ core →
      CoreClusteringEstimate dataSet core

open UniformDenseCoreClustering public

clusteringKillsSubgapOnDenseCore :
  ∀ {CoreVector HilbertVector}
    {dataSet : DenseCoreProjectionData CoreVector HilbertVector} →
  UniformDenseCoreClustering dataSet →
  ∀ core →
  positiveSubgapProjection dataSet (includeCore dataSet core)
  ≡ zeroVector dataSet
clusteringKillsSubgapOnDenseCore {dataSet = dataSet} clustered core =
  clusteringKillsSubgapProjection dataSet core
    (clusteringOnEveryCoreVector clustered core)

DenseCoreSpectralExclusion :
  ∀ {CoreVector HilbertVector} →
  DenseCoreProjectionData CoreVector HilbertVector → Set
DenseCoreSpectralExclusion dataSet = ∀ vector →
  positiveSubgapProjection dataSet vector ≡ zeroVector dataSet

denseLocalClusteringImpliesGap :
  ∀ {CoreVector HilbertVector}
    (dataSet : DenseCoreProjectionData CoreVector HilbertVector) →
  UniformDenseCoreClustering dataSet →
  DenseCoreSpectralExclusion dataSet
denseLocalClusteringImpliesGap dataSet clustered =
  denseContinuousExtension dataSet
    (clusteringKillsSubgapOnDenseCore clustered)

record PositiveDenseCoreGap
    {CoreVector HilbertVector : Set}
    (dataSet : DenseCoreProjectionData CoreVector HilbertVector)
    (CandidateGapPositive : Set) : Set₁ where
  field
    candidateGapPositive : CandidateGapPositive
    noPositiveSubgapSpectrum : DenseCoreSpectralExclusion dataSet

open PositiveDenseCoreGap public

positiveDenseCoreGapFromClustering :
  ∀ {CoreVector HilbertVector CandidateGapPositive}
    (dataSet : DenseCoreProjectionData CoreVector HilbertVector) →
  UniformDenseCoreClustering dataSet →
  CandidateGapPositive →
  PositiveDenseCoreGap dataSet CandidateGapPositive
positiveDenseCoreGapFromClustering
    dataSet clustered positiveGap = record
  { candidateGapPositive = positiveGap
  ; noPositiveSubgapSpectrum =
      denseLocalClusteringImpliesGap dataSet clustered
  }

denseCoreSpectralExclusionLevel : ProofLevel
denseCoreSpectralExclusionLevel = machineChecked

physicalDenseCoreAndContinuityInputsLevel : ProofLevel
physicalDenseCoreAndContinuityInputsLevel = conditional
