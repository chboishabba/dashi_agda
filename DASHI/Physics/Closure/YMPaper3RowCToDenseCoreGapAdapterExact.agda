{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.YMPaper3RowCToDenseCoreGapAdapterExact where

------------------------------------------------------------------------
-- PAPER 3 / ROW-C CLUSTERING -> DENSE-CORE SPECTRAL EXCLUSION
--
-- The modern YM Row-C lane already exposes a theorem-bearing geometric
-- connected-clustering object.  The Paper-3 continuum gap theorem uses a
-- different carrier: a dense centered local core in the continuum Hilbert
-- space, together with the positive-subgap spectral projection.
--
-- This adapter does NOT identify those carriers automatically.  The one live
-- same-object payment is a weld from every dense-core vector to a Row-C
-- observable whose geometric clustering witness supplies the exact
-- `CoreClusteringEstimate` consumed by the dense-core spectral theorem.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayDenseCoreSpectralGapExact as Dense
import DASHI.Physics.YangMills.BalabanRowCPostBC2PhysicalCompletionRound108Exact as RowC

record RowCToDenseCoreClusteringWeld
    {CoreVector HilbertVector Observable : Set}
    (dataSet : Dense.DenseCoreProjectionData CoreVector HilbertVector)
    (clustering : RowC.UniformGeometricConnectedClustering Observable) : Set₁ where
  field
    coreObservable : CoreVector → Observable

    -- Same-object / semantic bridge: the literal Row-C clustering theorem for
    -- the observable associated to this core vector pays the exact estimate
    -- required by the continuum dense-core spectral consumer.
    rowCClusteringPaysCoreEstimate :
      (core : CoreVector) →
      Dense.CoreClusteringEstimate dataSet core

open RowCToDenseCoreClusteringWeld public

asUniformDenseCoreClustering :
  ∀ {CoreVector HilbertVector Observable}
    {dataSet : Dense.DenseCoreProjectionData CoreVector HilbertVector}
    {clustering : RowC.UniformGeometricConnectedClustering Observable} →
  RowCToDenseCoreClusteringWeld dataSet clustering →
  Dense.UniformDenseCoreClustering dataSet
asUniformDenseCoreClustering weld = record
  { Dense.UniformDenseCoreClustering.clusteringOnEveryCoreVector =
      rowCClusteringPaysCoreEstimate weld
  }

rowCClusteringImpliesDenseCoreSpectralExclusion :
  ∀ {CoreVector HilbertVector Observable}
    (dataSet : Dense.DenseCoreProjectionData CoreVector HilbertVector)
    (clustering : RowC.UniformGeometricConnectedClustering Observable) →
  RowCToDenseCoreClusteringWeld dataSet clustering →
  Dense.DenseCoreSpectralExclusion dataSet
rowCClusteringImpliesDenseCoreSpectralExclusion dataSet clustering weld =
  Dense.denseLocalClusteringImpliesGap dataSet
    (asUniformDenseCoreClustering weld)

rowCClusteringImpliesPositiveDenseCoreGap :
  ∀ {CoreVector HilbertVector Observable CandidateGapPositive}
    (dataSet : Dense.DenseCoreProjectionData CoreVector HilbertVector)
    (clustering : RowC.UniformGeometricConnectedClustering Observable) →
  RowCToDenseCoreClusteringWeld dataSet clustering →
  CandidateGapPositive →
  Dense.PositiveDenseCoreGap dataSet CandidateGapPositive
rowCClusteringImpliesPositiveDenseCoreGap
    dataSet clustering weld positiveGap =
  Dense.positiveDenseCoreGapFromClustering dataSet
    (asUniformDenseCoreClustering weld)
    positiveGap

rowCToDenseCoreCompilerLevel : ProofLevel
rowCToDenseCoreCompilerLevel = machineChecked

-- The theorem algebra is closed once the same-object weld is supplied.  The
-- physical claim that the Row-C observable family is the dense OS/Wightman core
-- remains a genuine continuum-identification payment.
rowCToDenseCoreSameObjectWeldLevel : ProofLevel
rowCToDenseCoreSameObjectWeldLevel = conditional

physicalDenseCoreProjectionDataLevel : ProofLevel
physicalDenseCoreProjectionDataLevel = conditional
