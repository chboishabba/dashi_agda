module DASHI.Core.CanonicalSpineDependencyAtlasExact where

open import DASHI.Core.Prelude

import DASHI.Core.CanonicalSpineRegistry as Registry
import DASHI.Core.TypedDependencyCore as Dependency

------------------------------------------------------------------------
-- TYPED DEPENDENCIES BETWEEN CANONICAL SPINES
--
-- This is deliberately not another generic relationship enum.  The generic
-- relation/witness machinery already lives in TypedDependencyCore.  We only
-- state the small set of canonical parent dependencies currently paid by the
-- repository archaeology and formal interfaces.
--
-- Direction convention:
--   CanonicalDependency child parent
-- means the child structurally/provenance-wise depends on or refines the parent
-- for the stated scope.  It does NOT mean theorem equivalence, definitionally
-- identical carriers, or a literal Agda import edge.
------------------------------------------------------------------------

data CanonicalDependency :
    Registry.CanonicalOwner → Registry.CanonicalOwner → Set where
  consumerRepairDependsOnObserverRefinement :
    CanonicalDependency
      Registry.consumerFibreRepairOwner
      Registry.observerRefinementOwner

  frozenDynamicDependsOnObserverRefinement :
    CanonicalDependency
      Registry.frozenProvenanceDynamicOwner
      Registry.observerRefinementOwner

  requiredAxisJoinDependsOnQueryAdequacy :
    CanonicalDependency
      Registry.requiredObserverAxisJoinOwner
      Registry.queryIndexedProjectionOwner

  boundedNegativeSearchDependsOnOSINT :
    CanonicalDependency
      Registry.boundedNegativeSearchOwner
      Registry.osintAcquisitionOwner

  attributionSnowballDependsOnAttributedSource :
    CanonicalDependency
      Registry.attributionSnowballOwner
      Registry.attributedSourceOwner

  requirementBatchDependsOnCandidateExecution :
    CanonicalDependency
      Registry.requirementConflictBatchOwner
      Registry.candidateFamilyExecutionOwner

  futureSafePromotionDependsOnQueryAdequacy :
    CanonicalDependency
      Registry.queryIndexedFutureSafePromotionOwner
      Registry.queryIndexedProjectionOwner

  futureSafePromotionDependsOnFrozenDynamic :
    CanonicalDependency
      Registry.queryIndexedFutureSafePromotionOwner
      Registry.frozenProvenanceDynamicOwner

------------------------------------------------------------------------
-- Proof-bearing dependency receipts reuse TypedDependencyCore directly.
------------------------------------------------------------------------

consumerRepairObserverDependencyWitness :
  Dependency.DependencyWitness CanonicalDependency
consumerRepairObserverDependencyWitness =
  Dependency.dependencyWitness
    Registry.consumerFibreRepairOwner
    Registry.observerRefinementOwner
    consumerRepairDependsOnObserverRefinement
    Dependency.epistemicLayer
    Dependency.requiredDependency
    "ConsumerFibreRepairExact reuses ObserverRefinementLatticeExact.pairObserver as the single canonical pairing/refinement carrier and adds consumer-specific sufficiency obligations over that observer refinement."
    "observer pairing and refinement only; consumer sufficiency/non-descent remains owned by the repair/descent layer"

frozenDynamicObserverDependencyWitness :
  Dependency.DependencyWitness CanonicalDependency
frozenDynamicObserverDependencyWitness =
  Dependency.dependencyWitness
    Registry.frozenProvenanceDynamicOwner
    Registry.observerRefinementOwner
    frozenDynamicDependsOnObserverRefinement
    Dependency.epistemicLayer
    Dependency.requiredDependency
    "FrozenProvenanceDynamicRefinementExact constructs provenance joins and strict refinements using ObserverRefinementLatticeExact, then adds frozen-selection and independent dynamic-safety payments."
    "static observer refinement coordinate only; frozen methodology and dynamic safety remain separate child obligations"

requiredAxisJoinDependencyWitness :
  Dependency.DependencyWitness CanonicalDependency
requiredAxisJoinDependencyWitness =
  Dependency.dependencyWitness
    Registry.requiredObserverAxisJoinOwner
    Registry.queryIndexedProjectionOwner
    requiredAxisJoinDependsOnQueryAdequacy
    Dependency.epistemicLayer
    Dependency.requiredDependency
    "RequiredObserverAxisJoinAdequacyExact extends the query-relative adequacy discipline to multiple declared observer axes and constructs the exact product factorisation when both are retained."
    "joint observer adequacy for declared consumer axes only; it does not establish world completeness"

boundedNegativeSearchDependencyWitness :
  Dependency.DependencyWitness CanonicalDependency
boundedNegativeSearchDependencyWitness =
  Dependency.dependencyWitness
    Registry.boundedNegativeSearchOwner
    Registry.osintAcquisitionOwner
    boundedNegativeSearchDependsOnOSINT
    Dependency.epistemicLayer
    Dependency.requiredDependency
    "SnowballOSINTAcquisitionInvariantExact owns the qualitative non-location firewall; BoundedNegativeSearchExact strictly refines that repository lesson with proof-valued scope and an explicit universe-coverage promotion gate."
    "structural/provenance parentage for negative-search acquisition semantics only; the generic bounded-search theorem remains mathematically standalone and does not import OSINT"

attributionSnowballDependencyWitness :
  Dependency.DependencyWitness CanonicalDependency
attributionSnowballDependencyWitness =
  Dependency.dependencyWitness
    Registry.attributionSnowballOwner
    Registry.attributedSourceOwner
    attributionSnowballDependsOnAttributedSource
    Dependency.provenanceLayer
    Dependency.requiredDependency
    "Snowball attribution retains attributed-source identity, source role, visibility, proof non-import, and authority non-creation."
    "attribution/provenance retention; citation does not create theorem or domain authority"

requirementBatchDependencyWitness :
  Dependency.DependencyWitness CanonicalDependency
requirementBatchDependencyWitness =
  Dependency.dependencyWitness
    Registry.requirementConflictBatchOwner
    Registry.candidateFamilyExecutionOwner
    requirementBatchDependsOnCandidateExecution
    Dependency.operationalLayer
    Dependency.requiredDependency
    "Requirement/conflict batching refines candidate-family execution by adding relation classification and closure obligations before the independent global execution check."
    "selected-family execution; relation semantics remain application supplied"

futureSafeQueryDependencyWitness :
  Dependency.DependencyWitness CanonicalDependency
futureSafeQueryDependencyWitness =
  Dependency.dependencyWitness
    Registry.queryIndexedFutureSafePromotionOwner
    Registry.queryIndexedProjectionOwner
    futureSafePromotionDependsOnQueryAdequacy
    Dependency.epistemicLayer
    Dependency.requiredDependency
    "Future-safe promotion requires the refined observer to be adequate for the declared query, not merely to separate one witnessed collision."
    "consumer/query adequacy coordinate"

futureSafeDynamicDependencyWitness :
  Dependency.DependencyWitness CanonicalDependency
futureSafeDynamicDependencyWitness =
  Dependency.dependencyWitness
    Registry.queryIndexedFutureSafePromotionOwner
    Registry.frozenProvenanceDynamicOwner
    futureSafePromotionDependsOnFrozenDynamic
    Dependency.temporalLayer
    Dependency.requiredDependency
    "Future-safe promotion retains provenance-aware strict refinement, frozen selection, and dynamic trace safety from the frozen/dynamic parent."
    "future trace congruence and frozen-selection coordinate"

------------------------------------------------------------------------
-- Boundary: this atlas is intentionally incomplete and append-only.  Missing
-- edges remain missing rather than being inferred from names, imports, shared
-- vocabulary, or conceptual resemblance.
------------------------------------------------------------------------

record CanonicalDependencyAtlasBoundary : Set where
  constructor canonical-dependency-atlas-boundary
  field
    usesTypedDependencyCore : Bool
    onlyPaidEdgesRecorded : Bool
    importRelationshipAutomaticallyCreatesDependency : Bool
    conceptualResemblanceAutomaticallyCreatesDependency : Bool
    childDependencyImpliesTheoremEquivalence : Bool
    structuralParentageImpliesCodeImportDependency : Bool

canonicalDependencyAtlasBoundary : CanonicalDependencyAtlasBoundary
canonicalDependencyAtlasBoundary =
  canonical-dependency-atlas-boundary
    true
    true
    false
    false
    false
    false
