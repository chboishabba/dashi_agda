module DASHI.Core.CanonicalSpineDependencyAtlasRegression where

open import DASHI.Core.Prelude

import DASHI.Core.CanonicalSpineRegistry as Registry
import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.CanonicalSpineDependencyAtlasExact as Atlas

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

boundedSearchDependencyWitness :
  Dependency.DependencyWitness Atlas.CanonicalDependency
boundedSearchDependencyWitness = Atlas.boundedNegativeSearchDependencyWitness

futureSafeQueryDependencyWitness :
  Dependency.DependencyWitness Atlas.CanonicalDependency
futureSafeQueryDependencyWitness = Atlas.futureSafeQueryDependencyWitness
