{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5CoreClusteringAttachmentRound429Exact where

------------------------------------------------------------------------
-- ROUND429 / ATTACH P1 CLUSTERING TO THE PRE-GAP CONTINUUM CORE
--
-- R428 now constructs the same-family continuum/OS CORE without clustering.
-- This module is the only preferred attachment point for clustering:
--
--   P1 finite clustering / selected covariance bound
--   + P2 interpretation on the SAME selected continuum family
--   ---------------------------------------------------------
--   SelectedContinuumClustering core
--
-- Only after this object exists may the legacy clustered OS carrier be rebuilt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5SelectedContinuumOSExact as Selected
import DASHI.Physics.YangMills.BalabanClayT5ConditionalClusteringCutsetExact as Clustering

record CoreClusteringAttachment
    {Measure Schwinger Observable Scalar : Set}
    (core : Selected.SelectedFiniteToContinuumOSCore Measure Schwinger) : Set₁ where
  field
    clusteringCutset :
      Clustering.ConditionalClusteringAssembly Observable Scalar

    Clustered : Schwinger → Set

    -- Exact P2/same-family meaning theorem.  No independent clustering
    -- assumption is stored in the core.
    selectedBoundMeansCoreClustered :
      ((left right : Observable) →
        Clustering.LessEqual clusteringCutset
          (Clustering.covariance clusteringCutset left right)
          (Clustering.targetClusteringBound clusteringCutset left right)) →
      Clustered
        (Selected.schwingerCore core
          (Selected.continuumMeasureCore core))

open CoreClusteringAttachment public

selectedContinuumClustering :
  ∀ {Measure Schwinger Observable Scalar}
    {core : Selected.SelectedFiniteToContinuumOSCore Measure Schwinger} →
  CoreClusteringAttachment {Observable = Observable} {Scalar = Scalar} core →
  Selected.SelectedContinuumClustering core
selectedContinuumClustering attachment = record
  { Selected.SelectedContinuumClustering.ClusteredCore =
      Clustered attachment
  ; Selected.SelectedContinuumClustering.continuumClusteredCore =
      selectedBoundMeansCoreClustered attachment
        (Clustering.conditionalUniformClustering
          (clusteringCutset attachment))
  }

fullSelectedOSAfterClustering :
  ∀ {Measure Schwinger Observable Scalar}
    {core : Selected.SelectedFiniteToContinuumOSCore Measure Schwinger} →
  CoreClusteringAttachment {Observable = Observable} {Scalar = Scalar} core →
  Selected.SelectedFiniteToContinuumOS Measure Schwinger
fullSelectedOSAfterClustering {core = core} attachment =
  Selected.corePlusClusteringToFullSelectedOS core
    (selectedContinuumClustering attachment)

round429ClusteringAttachmentCompilerLevel : ProofLevel
round429ClusteringAttachmentCompilerLevel = machineChecked

round429ContinuumClusteringMeaningLevel : ProofLevel
round429ContinuumClusteringMeaningLevel = conditional

round429IndependentH2ClusteringInputRequired : Bool
round429IndependentH2ClusteringInputRequired = false

round429ClusteringRequiredForCoreConstruction : Bool
round429ClusteringRequiredForCoreConstruction = false
