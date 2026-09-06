module DASHI.Biology.DrosophilaAmplificationLineageAggregationBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.DrosophilaSameTrialProvenanceDependenceExact as Fly
import DASHI.Core.AmplificationLineageBidiCrossPollination2026Exact as Lineage

------------------------------------------------------------------------
-- RECIPROCAL WELD: DROSOPHILA DEPENDENCE <-> AMPLIFICATION LINEAGE
--
-- The fly owner already separates within-dependence-class aggregation from
-- aggregation across independent classes.  The lineage owner adds semantics to
-- the path connecting visible descendants to their upstream producer/root.
-- A shared lineage root therefore supplies a reason to remain in the
-- within-class lane; descendant multiplicity does not manufacture replication.
------------------------------------------------------------------------

record LineageAwareDependenceUnit : Set where
  constructor lineage-aware-dependence-unit
  field
    node : Lineage.LineageNode
    dependenceRelation : Fly.EvidenceRelation
    dependencyClassReference : String
    residualReference : String
open LineageAwareDependenceUnit public

record SharedRootAggregationReceipt
    (left right : LineageAwareDependenceUnit) : Set where
  constructor shared-root-aggregation-receipt
  field
    sharedRoot : Lineage.SharedRootWitness (node left) (node right)
    sameDependenceClassReference : String
    aggregateWithinClass : Bool
    aggregateWithinClassIsTrue : aggregateWithinClass ≡ true
open SharedRootAggregationReceipt public

record IndependentClassAggregationReceipt
    (left right : LineageAwareDependenceUnit) : Set where
  constructor independent-class-aggregation-receipt
  field
    independence : Lineage.IndependenceReceipt (node left) (node right)
    differentDependenceClassReference : String
    aggregateAcrossIndependentClasses : Bool
    aggregateAcrossIndependentClassesIsTrue :
      aggregateAcrossIndependentClasses ≡ true
open IndependentClassAggregationReceipt public

record DrosophilaAggregationWeld : Set₁ where
  constructor drosophila-aggregation-weld
  field
    donorAggregation : Fly.DependenceAwareResidualAggregation
    lineageReading : String
    withinClassNeedsDependenceEvidence : Bool
    withinClassNeedsDependenceEvidenceIsTrue :
      withinClassNeedsDependenceEvidence ≡ true
    crossClassNeedsIndependenceReceipt : Bool
    crossClassNeedsIndependenceReceiptIsTrue :
      crossClassNeedsIndependenceReceipt ≡ true
open DrosophilaAggregationWeld public

data DescendantCountCreatesIndependentReplication : Set where

descendantCountDoesNotCreateIndependentReplication :
  DescendantCountCreatesIndependentReplication → ⊥
descendantCountDoesNotCreateIndependentReplication ()

record DrosophilaLineageAggregationBoundary : Set where
  constructor drosophila-lineage-aggregation-boundary
  field
    sharedRootRoutesWithinClass : Bool
    independenceReceiptRoutesAcrossClasses : Bool
    repeatedDescendantsDoNotCreateReplication : Bool

canonicalDrosophilaLineageAggregationBoundary :
  DrosophilaLineageAggregationBoundary
canonicalDrosophilaLineageAggregationBoundary =
  drosophila-lineage-aggregation-boundary true true true
