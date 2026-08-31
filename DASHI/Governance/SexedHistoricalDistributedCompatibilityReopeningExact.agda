module DASHI.Governance.SexedHistoricalDistributedCompatibilityReopeningExact where

------------------------------------------------------------------------
-- DISTRIBUTED SELECTIVE REOPENING OVER STRATIFIED LOCAL/GLOBAL HISTORIES
--
-- A local branch/action change can alter another subject's ecology and a global
-- compatibility receipt without invalidating every local certificate.  The
-- affected region is determined by a proof-bearing dependency path.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Core.AdaptiveConsumerModelLoopExact as Adaptive
import DASHI.Governance.SexedHistoricalStratifiedCollectiveGluingExact as Gluing
import DASHI.Governance.SexedHistoricalBracketedMultiverseTSFVBridgeExact as Branching

------------------------------------------------------------------------
-- 1. Distributed historical artifacts.
------------------------------------------------------------------------

data DistributedArtifact : Set where
  feminineEnactedBranch
  masculineEcologyCertificate
  masculineOptionConeCertificate
  feminineLocalCertificate
  masculineLocalCertificate
  institutionalLocalCertificate
  globalCompatibilityCertificate
  globalContinuationCertificate
  collectiveFutureConeCertificate
  sourceAttributionCertificate
  : DistributedArtifact

------------------------------------------------------------------------
-- 2. Dependency graph.
--
-- The canonical finite path models one co-constitutive route:
-- feminine enactment -> masculine ecology -> masculine option cone -> global
-- compatibility -> global continuation -> collective future cone.
--
-- Feminine local provenance and source attribution are deliberately outside
-- that path.  This is a DASHI finite dependency fixture, not an empirical law.
------------------------------------------------------------------------

data Depends : DistributedArtifact → DistributedArtifact → Set where
  feminineActionAffectsMasculineEcology :
    Depends feminineEnactedBranch masculineEcologyCertificate
  masculineEcologyAffectsOptionCone :
    Depends masculineEcologyCertificate masculineOptionConeCertificate
  masculineOptionConeAffectsCompatibility :
    Depends masculineOptionConeCertificate globalCompatibilityCertificate
  feminineLocalAffectsCompatibility :
    Depends feminineLocalCertificate globalCompatibilityCertificate
  masculineLocalAffectsCompatibility :
    Depends masculineLocalCertificate globalCompatibilityCertificate
  institutionalLocalAffectsCompatibility :
    Depends institutionalLocalCertificate globalCompatibilityCertificate
  compatibilityAffectsGlobalContinuation :
    Depends globalCompatibilityCertificate globalContinuationCertificate
  globalContinuationAffectsFutureCone :
    Depends globalContinuationCertificate collectiveFutureConeCertificate

------------------------------------------------------------------------
-- 3. Transitive affected-closure receipts from one enacted local branch.
------------------------------------------------------------------------

masculineEcologyMustReopen :
  Dependency.ReopeningObligation
    Depends feminineEnactedBranch masculineEcologyCertificate
masculineEcologyMustReopen =
  Dependency.oneEdgeCreatesReopeningObligation
    feminineActionAffectsMasculineEcology

masculineOptionConeMustReopen :
  Dependency.ReopeningObligation
    Depends feminineEnactedBranch masculineOptionConeCertificate
masculineOptionConeMustReopen =
  Dependency.obligationsCompose
    masculineEcologyMustReopen
    (Dependency.oneEdgeCreatesReopeningObligation
      masculineEcologyAffectsOptionCone)

globalCompatibilityMustReopenFromFeminineEnactment :
  Dependency.ReopeningObligation
    Depends feminineEnactedBranch globalCompatibilityCertificate
globalCompatibilityMustReopenFromFeminineEnactment =
  Dependency.obligationsCompose
    masculineOptionConeMustReopen
    (Dependency.oneEdgeCreatesReopeningObligation
      masculineOptionConeAffectsCompatibility)

globalContinuationMustReopenFromFeminineEnactment :
  Dependency.ReopeningObligation
    Depends feminineEnactedBranch globalContinuationCertificate
globalContinuationMustReopenFromFeminineEnactment =
  Dependency.obligationsCompose
    globalCompatibilityMustReopenFromFeminineEnactment
    (Dependency.oneEdgeCreatesReopeningObligation
      compatibilityAffectsGlobalContinuation)

collectiveFutureConeMustReopenFromFeminineEnactment :
  Dependency.ReopeningObligation
    Depends feminineEnactedBranch collectiveFutureConeCertificate
collectiveFutureConeMustReopenFromFeminineEnactment =
  Dependency.obligationsCompose
    globalContinuationMustReopenFromFeminineEnactment
    (Dependency.oneEdgeCreatesReopeningObligation
      globalContinuationAffectsFutureCone)

canonicalDistributedReopening :
  Adaptive.SelectiveCertificateReopening
    DistributedArtifact Depends feminineEnactedBranch
canonicalDistributedReopening =
  Adaptive.selectiveCertificateReopening
    collectiveFutureConeCertificate
    (Dependency.dependencyPath collectiveFutureConeMustReopenFromFeminineEnactment)
    "local enactment reopens only its proof-bearing co-constitutive/global dependency cone"

------------------------------------------------------------------------
-- 4. Institutional local repair can reopen global compatibility without
-- touching unrelated local-history/source certificates.
------------------------------------------------------------------------

institutionalChangeReopensGlobalCompatibility :
  Dependency.ReopeningObligation
    Depends institutionalLocalCertificate globalCompatibilityCertificate
institutionalChangeReopensGlobalCompatibility =
  Dependency.oneEdgeCreatesReopeningObligation
    institutionalLocalAffectsCompatibility

institutionalChangeReopensGlobalContinuation :
  Dependency.ReopeningObligation
    Depends institutionalLocalCertificate globalContinuationCertificate
institutionalChangeReopensGlobalContinuation =
  Dependency.obligationsCompose
    institutionalChangeReopensGlobalCompatibility
    (Dependency.oneEdgeCreatesReopeningObligation
      compatibilityAffectsGlobalContinuation)

------------------------------------------------------------------------
-- 5. Concrete compatibility-threshold continuity.
------------------------------------------------------------------------

canonicalCompatibilityRepair : Gluing.MinimalCompatibilityExtension
canonicalCompatibilityRepair = Gluing.canonicalMinimalCompatibilityExtension

canonicalGlobalAfterCompatibilityRepair : Gluing.GlobalContinuation
canonicalGlobalAfterCompatibilityRepair = Gluing.canonicalGlobalContinuation

canonicalDescendantFutureStillBranches :
  Branching.BracketedMultiverseTSFVBoundary
canonicalDescendantFutureStillBranches =
  Branching.canonicalBracketedMultiverseTSFVBoundary

------------------------------------------------------------------------
-- 6. No-promotion boundaries.
------------------------------------------------------------------------

data LocalActionDeterminesOtherSubjectAction : Set where

data LocalActionReopensEveryLocalCertificate : Set where

data InstitutionalRepairErasesLocalHistories : Set where

data DistributedReopeningGuaranteesGlobalAgreement : Set where

data GlobalCompatibilityMeansUniformLocalBranch : Set where

data SourceAttributionChangesBecauseLocalActionChanged : Set where

data AffectedDependencyPathIsEmpiricalCausalLaw : Set where

localActionDoesNotDetermineOtherSubjectAction :
  LocalActionDeterminesOtherSubjectAction → ⊥
localActionDoesNotDetermineOtherSubjectAction ()

localActionDoesNotReopenEverything :
  LocalActionReopensEveryLocalCertificate → ⊥
localActionDoesNotReopenEverything ()

institutionalRepairDoesNotEraseLocalHistories :
  InstitutionalRepairErasesLocalHistories → ⊥
institutionalRepairDoesNotEraseLocalHistories ()

distributedReopeningDoesNotGuaranteeGlobalAgreement :
  DistributedReopeningGuaranteesGlobalAgreement → ⊥
distributedReopeningDoesNotGuaranteeGlobalAgreement ()

globalCompatibilityDoesNotRequireUniformLocalBranch :
  GlobalCompatibilityMeansUniformLocalBranch → ⊥
globalCompatibilityDoesNotRequireUniformLocalBranch ()

localActionDoesNotRewriteSourceAttribution :
  SourceAttributionChangesBecauseLocalActionChanged → ⊥
localActionDoesNotRewriteSourceAttribution ()

dependencyFixtureIsNotEmpiricalCausalLaw :
  AffectedDependencyPathIsEmpiricalCausalLaw → ⊥
dependencyFixtureIsNotEmpiricalCausalLaw ()

record DistributedCompatibilityReopeningBoundary : Set where
  constructor distributed-compatibility-reopening-boundary
  field
    oneLocalActionCanAffectAnotherLocalOptionCone : Bool
    proofBearingDependencyClosureUsed : Bool
    affectedGlobalCompatibilityCanReopen : Bool
    everyLocalCertificateReopens : Bool
    globalCompatibilityRequiresLocalUniformity : Bool
    localActionDeterminesOtherSubjectAction : Bool
    institutionalRepairErasesLocalHistories : Bool
    sourceAttributionChangesWithLocalAction : Bool
    dependencyGraphIsEmpiricalCausalLaw : Bool

canonicalDistributedCompatibilityReopeningBoundary :
  DistributedCompatibilityReopeningBoundary
canonicalDistributedCompatibilityReopeningBoundary =
  distributed-compatibility-reopening-boundary
    true true true false false false false false false
