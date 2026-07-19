module DASHI.Biology.Cannabis.TerpeneClusteringStudyReceipt where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Biology.Cannabis.TerpeneClusterPromotionBoundary

-- This layer binds the abstract six-cluster surface to an empirical study.
-- It deliberately records method, cohort, preprocessing, model selection, and
-- stability separately from any effect claim.
record TerpeneClusteringStudyReceipt
  (Source Cohort Sample Terpene Coordinate Preprocessing Method
   SelectionCriterion StabilityEvidence : Set) : Set₁ where
  field
    source              : Source
    cohort              : Cohort
    samples             : Sample → Set
    measuredCoordinate  : Coordinate → Terpene
    preprocessing       : Preprocessing
    clusteringMethod    : Method
    selectionCriterion  : SelectionCriterion
    requestedClusters   : Nat
    selectedClusters    : Nat
    sixClustersSelected : selectedClusters ≡ 6
    stabilityEvidence   : StabilityEvidence
    chemicalReceipt     : ChemicalClusterReceipt Sample Terpene

-- A six-cluster study receipt proves only a source-bound chemical partition.
-- It contains no field from clusters or traditional labels to effects.
record StudyAuthorityBoundary
  (Source Cohort Sample Terpene Coordinate Preprocessing Method
   SelectionCriterion StabilityEvidence : Set) : Set₁ where
  field
    study : TerpeneClusteringStudyReceipt Source Cohort Sample Terpene Coordinate
      Preprocessing Method SelectionCriterion StabilityEvidence
    labelsObservedSeparately : LabelObservation Sample

selected-six-is-chemical-arity :
  {Source Cohort Sample Terpene Coordinate Preprocessing Method
   SelectionCriterion StabilityEvidence : Set} →
  (r : TerpeneClusteringStudyReceipt Source Cohort Sample Terpene Coordinate
    Preprocessing Method SelectionCriterion StabilityEvidence) →
  TerpeneClusteringStudyReceipt.selectedClusters r ≡ 6
selected-six-is-chemical-arity r =
  TerpeneClusteringStudyReceipt.sixClustersSelected r

-- Explicit negative-space record: any proposed label or effect bridge must be
-- supplied later as a new receipt rather than silently inferred from the study.
record ProposedBridge (A B : Set) : Set₁ where
  field
    map       : A → B
    justified : Set
    witness   : justified
