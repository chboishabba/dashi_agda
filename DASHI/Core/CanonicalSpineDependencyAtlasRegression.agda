module DASHI.Core.CanonicalSpineDependencyAtlasRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.CanonicalSpineRegistry as Registry
import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.CanonicalSpineDependencyAtlasExact as Atlas

consumerRepairObserverRelation :
  Atlas.CanonicalDependency
    Registry.consumerFibreRepairOwner
    Registry.observerRefinementOwner
consumerRepairObserverRelation = Atlas.consumerRepairDependsOnObserverRefinement

frozenDynamicObserverRelation :
  Atlas.CanonicalDependency
    Registry.frozenProvenanceDynamicOwner
    Registry.observerRefinementOwner
frozenDynamicObserverRelation = Atlas.frozenDynamicDependsOnObserverRefinement

requiredAxisJoinObserverRelation :
  Atlas.CanonicalDependency
    Registry.requiredObserverAxisJoinOwner
    Registry.observerRefinementOwner
requiredAxisJoinObserverRelation = Atlas.requiredAxisJoinDependsOnObserverRefinement

requiredAxisJoinRelation :
  Atlas.CanonicalDependency
    Registry.requiredObserverAxisJoinOwner
    Registry.queryIndexedProjectionOwner
requiredAxisJoinRelation = Atlas.requiredAxisJoinDependsOnQueryAdequacy

boundedSearchRelation :
  Atlas.CanonicalDependency
    Registry.boundedNegativeSearchOwner
    Registry.osintAcquisitionOwner
boundedSearchRelation = Atlas.boundedNegativeSearchDependsOnOSINT

snowballAttributionRelation :
  Atlas.CanonicalDependency
    Registry.attributionSnowballOwner
    Registry.attributedSourceOwner
snowballAttributionRelation = Atlas.attributionSnowballDependsOnAttributedSource

batchExecutionRelation :
  Atlas.CanonicalDependency
    Registry.requirementConflictBatchOwner
    Registry.candidateFamilyExecutionOwner
batchExecutionRelation = Atlas.requirementBatchDependsOnCandidateExecution

futureSafeQueryRelation :
  Atlas.CanonicalDependency
    Registry.queryIndexedFutureSafePromotionOwner
    Registry.queryIndexedProjectionOwner
futureSafeQueryRelation = Atlas.futureSafePromotionDependsOnQueryAdequacy

futureSafeDynamicRelation :
  Atlas.CanonicalDependency
    Registry.queryIndexedFutureSafePromotionOwner
    Registry.frozenProvenanceDynamicOwner
futureSafeDynamicRelation = Atlas.futureSafePromotionDependsOnFrozenDynamic

consumerRepairObserverDependencyWitness :
  Dependency.DependencyWitness Atlas.CanonicalDependency
consumerRepairObserverDependencyWitness = Atlas.consumerRepairObserverDependencyWitness

frozenDynamicObserverDependencyWitness :
  Dependency.DependencyWitness Atlas.CanonicalDependency
frozenDynamicObserverDependencyWitness = Atlas.frozenDynamicObserverDependencyWitness

requiredAxisJoinObserverDependencyWitness :
  Dependency.DependencyWitness Atlas.CanonicalDependency
requiredAxisJoinObserverDependencyWitness = Atlas.requiredAxisJoinObserverDependencyWitness

requiredAxisJoinDependencyWitness :
  Dependency.DependencyWitness Atlas.CanonicalDependency
requiredAxisJoinDependencyWitness = Atlas.requiredAxisJoinDependencyWitness

boundedSearchDependencyWitness :
  Dependency.DependencyWitness Atlas.CanonicalDependency
boundedSearchDependencyWitness = Atlas.boundedNegativeSearchDependencyWitness

futureSafeQueryDependencyWitness :
  Dependency.DependencyWitness Atlas.CanonicalDependency
futureSafeQueryDependencyWitness = Atlas.futureSafeQueryDependencyWitness

structuralParentageIsNotImportDependency :
  Atlas.CanonicalDependencyAtlasBoundary.structuralParentageImpliesCodeImportDependency
    Atlas.canonicalDependencyAtlasBoundary ≡ false
structuralParentageIsNotImportDependency = refl
