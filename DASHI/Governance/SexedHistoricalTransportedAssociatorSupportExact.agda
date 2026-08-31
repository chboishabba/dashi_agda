module DASHI.Governance.SexedHistoricalTransportedAssociatorSupportExact where

------------------------------------------------------------------------
-- TRANSPORTED ASSOCIATOR SUPPORT OVER TIME
--
-- The support of a coalition associator is not frozen.  A later local repair,
-- network counterformation, or institutional response can preserve, discharge,
-- activate, split, merge, or relocate supported coordinates.  This owner makes
-- support itself history-indexed and transport-bearing.
--
-- Cross-pollination:
--   * associator-supported reopening supplies the initial sparse support;
--   * Base369 strata supply geometric coarse positions only;
--   * affected-dependency closure supplies consumer-qualified reopening;
--   * Yijing moving-line structure remains a sparse-change/provenance analogy,
--     not prediction or a historical causal mechanism.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Foundations.Base369Ternary27HypervoxelStratificationExact as Strata
import DASHI.Governance.SexedHistoricalAssociatorSupportedReopeningExact as Support
import DASHI.Governance.SexedHistoricalDistributedCompatibilityReopeningExact as Distributed

------------------------------------------------------------------------
-- 1. Historical support stages.
------------------------------------------------------------------------

data SupportStage : Set where
  initialAssociatorStage
  localRepairStage
  networkCounterformationStage
  institutionalPersistenceStage
  : SupportStage

data ActiveAt : SupportStage → Support.SignatureLine → Set where
  initialLine1 : ActiveAt initialAssociatorStage Support.line1
  initialLine4 : ActiveAt initialAssociatorStage Support.line4
  repairLine4 : ActiveAt localRepairStage Support.line4
  counterLine4 : ActiveAt networkCounterformationStage Support.line4
  counterLine5 : ActiveAt networkCounterformationStage Support.line5
  persistentLine4 : ActiveAt institutionalPersistenceStage Support.line4

------------------------------------------------------------------------
-- 2. Exact support evolution witnesses.
--
-- canonical history:
--   {1,4} -> {4} -> {4,5} -> {4}
------------------------------------------------------------------------

line1DischargedByLocalRepair : ActiveAt localRepairStage Support.line1 → ⊥
line1DischargedByLocalRepair ()

line4PersistsThroughLocalRepair : ActiveAt localRepairStage Support.line4
line4PersistsThroughLocalRepair = repairLine4

line5ActivatedByCounterformation :
  ActiveAt networkCounterformationStage Support.line5
line5ActivatedByCounterformation = counterLine5

line5LaterDischarged : ActiveAt institutionalPersistenceStage Support.line5 → ⊥
line5LaterDischarged ()

line4PersistsToFinalStage :
  ActiveAt institutionalPersistenceStage Support.line4
line4PersistsToFinalStage = persistentLine4

------------------------------------------------------------------------
-- 3. Support transport relation.
------------------------------------------------------------------------

data SupportTransport : SupportStage → SupportStage → Set where
  initialToRepair : SupportTransport initialAssociatorStage localRepairStage
  repairToCounterformation :
    SupportTransport localRepairStage networkCounterformationStage
  counterformationToPersistence :
    SupportTransport networkCounterformationStage institutionalPersistenceStage

data SupportTransportPath : SupportStage → SupportStage → Set where
  supportPathRefl : ∀ {s} → SupportTransportPath s s
  supportPathStep :
    ∀ {a b c} →
    SupportTransport a b →
    SupportTransportPath b c →
    SupportTransportPath a c

canonicalSupportHistory :
  SupportTransportPath initialAssociatorStage institutionalPersistenceStage
canonicalSupportHistory =
  supportPathStep initialToRepair
    (supportPathStep repairToCounterformation
      (supportPathStep counterformationToPersistence supportPathRefl))

------------------------------------------------------------------------
-- 4. Stratum transport of supported coordinates.
------------------------------------------------------------------------

supportStratum : SupportStage → Support.SignatureLine → Strata.VoxelStratum
supportStratum initialAssociatorStage Support.line1 = Strata.faceCentreStratum
supportStratum initialAssociatorStage Support.line4 = Strata.centreStratum
supportStratum localRepairStage Support.line4 = Strata.centreStratum
supportStratum networkCounterformationStage Support.line4 = Strata.centreStratum
supportStratum networkCounterformationStage Support.line5 = Strata.edgeCentreStratum
supportStratum institutionalPersistenceStage Support.line4 = Strata.centreStratum
supportStratum _ _ = Strata.cornerStratum

counterformationActivatesEdgeStratumSupport :
  supportStratum networkCounterformationStage Support.line5
  ≡ Strata.edgeCentreStratum
counterformationActivatesEdgeStratumSupport = refl

institutionalResidualStaysAtCentreStratum :
  supportStratum initialAssociatorStage Support.line4
  ≡ supportStratum institutionalPersistenceStage Support.line4
institutionalResidualStaysAtCentreStratum = refl

------------------------------------------------------------------------
-- 5. Stage-indexed support-to-artifact chart.
------------------------------------------------------------------------

stageArtifact :
  SupportStage → Support.SignatureLine → Distributed.DistributedArtifact
stageArtifact initialAssociatorStage Support.line1 = Distributed.feminineLocalCertificate
stageArtifact initialAssociatorStage Support.line4 = Distributed.institutionalLocalCertificate
stageArtifact localRepairStage Support.line4 = Distributed.institutionalLocalCertificate
stageArtifact networkCounterformationStage Support.line4 = Distributed.institutionalLocalCertificate
stageArtifact networkCounterformationStage Support.line5 = Distributed.masculineLocalCertificate
stageArtifact institutionalPersistenceStage Support.line4 = Distributed.institutionalLocalCertificate
stageArtifact _ _ = Distributed.sourceAttributionCertificate

line5CounterformationTargetsMasculineLocal :
  stageArtifact networkCounterformationStage Support.line5
  ≡ Distributed.masculineLocalCertificate
line5CounterformationTargetsMasculineLocal = refl

------------------------------------------------------------------------
-- 6. Reopening obligations follow the support present AT THAT STAGE.
------------------------------------------------------------------------

initialLine1ReopensCompatibility :
  Dependency.ReopeningObligation Distributed.Depends
    (stageArtifact initialAssociatorStage Support.line1)
    Distributed.globalCompatibilityCertificate
initialLine1ReopensCompatibility = Support.line1ReopensGlobalCompatibility

initialLine4ReopensCompatibility :
  Dependency.ReopeningObligation Distributed.Depends
    (stageArtifact initialAssociatorStage Support.line4)
    Distributed.globalCompatibilityCertificate
initialLine4ReopensCompatibility = Support.line4ReopensGlobalCompatibility

counterformationLine5ReopensCompatibility :
  Dependency.ReopeningObligation Distributed.Depends
    (stageArtifact networkCounterformationStage Support.line5)
    Distributed.globalCompatibilityCertificate
counterformationLine5ReopensCompatibility =
  Dependency.oneEdgeCreatesReopeningObligation
    Distributed.masculineLocalAffectsCompatibility

counterformationLine5ReopensCollectiveFuture :
  Dependency.ReopeningObligation Distributed.Depends
    (stageArtifact networkCounterformationStage Support.line5)
    Distributed.collectiveFutureConeCertificate
counterformationLine5ReopensCollectiveFuture =
  Dependency.obligationsCompose
    counterformationLine5ReopensCompatibility
    (Dependency.obligationsCompose
      (Dependency.oneEdgeCreatesReopeningObligation
        Distributed.compatibilityAffectsGlobalContinuation)
      (Dependency.oneEdgeCreatesReopeningObligation
        Distributed.globalContinuationAffectsFutureCone))

finalLine4StillReopensCollectiveFuture :
  Dependency.ReopeningObligation Distributed.Depends
    (stageArtifact institutionalPersistenceStage Support.line4)
    Distributed.collectiveFutureConeCertificate
finalLine4StillReopensCollectiveFuture = Support.line4ReopensCollectiveFuture

------------------------------------------------------------------------
-- 7. Same coarse support does not recover support history.
------------------------------------------------------------------------

data SupportHistoryFine : Set where
  repairedThenCounterformed
  counterformedThenRepaired
  : SupportHistoryFine

data CoarseSupportSurface : Set where
  onePersistentCentreResidual : CoarseSupportSurface

data FineSupportHistoryCode : Set where
  repairBeforeCounterformation counterformationBeforeRepair : FineSupportHistoryCode

coarseSupportSurface : SupportHistoryFine → CoarseSupportSurface
coarseSupportSurface _ = onePersistentCentreResidual

fineSupportHistoryCode : SupportHistoryFine → FineSupportHistoryCode
fineSupportHistoryCode repairedThenCounterformed = repairBeforeCounterformation
fineSupportHistoryCode counterformedThenRepaired = counterformationBeforeRepair

sameCoarseSupportCannotRecoverSupportHistory :
  INF.FactorsThrough coarseSupportSurface fineSupportHistoryCode → ⊥
sameCoarseSupportCannotRecoverSupportHistory =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      repairedThenCounterformed counterformedThenRepaired refl (λ ()))

------------------------------------------------------------------------
-- 8. No-promotion boundaries.
------------------------------------------------------------------------

data SupportPersistenceMeansHistoricalPermanence : Set where

data SupportDischargeMeansHistoricalIrrelevance : Set where

data SupportActivationProvesEmpiricalCause : Set where

data SameStratumMeansSameSupportHistory : Set where

data TransportedSupportIsYijingPrediction : Set where

data EveryFutureStageMustPreserveCurrentSupport : Set where

data SupportMigrationMeansSubjectIdentityMigration : Set where

supportPersistenceDoesNotMeanHistoricalPermanence :
  SupportPersistenceMeansHistoricalPermanence → ⊥
supportPersistenceDoesNotMeanHistoricalPermanence ()

supportDischargeDoesNotMeanHistoricalIrrelevance :
  SupportDischargeMeansHistoricalIrrelevance → ⊥
supportDischargeDoesNotMeanHistoricalIrrelevance ()

supportActivationDoesNotProveEmpiricalCause :
  SupportActivationProvesEmpiricalCause → ⊥
supportActivationDoesNotProveEmpiricalCause ()

sameStratumDoesNotMeanSameSupportHistory :
  SameStratumMeansSameSupportHistory → ⊥
sameStratumDoesNotMeanSameSupportHistory ()

transportedSupportIsNotYijingPrediction :
  TransportedSupportIsYijingPrediction → ⊥
transportedSupportIsNotYijingPrediction ()

futureStagesNeedNotPreserveCurrentSupport :
  EveryFutureStageMustPreserveCurrentSupport → ⊥
futureStagesNeedNotPreserveCurrentSupport ()

supportMigrationDoesNotMeanSubjectIdentityMigration :
  SupportMigrationMeansSubjectIdentityMigration → ⊥
supportMigrationDoesNotMeanSubjectIdentityMigration ()

record TransportedAssociatorSupportBoundary : Set where
  constructor transported-associator-support-boundary
  field
    supportIsHistoryIndexed : Bool
    supportCanShrink : Bool
    supportCanActivateNewCoordinate : Bool
    supportCanPersist : Bool
    supportCanLaterDischarge : Bool
    stageSpecificSupportDrivesReopening : Bool
    sameCoarseSupportRecoversHistory : Bool
    strataCarryIntrinsicSocialMeaning : Bool
    supportTransportIsPrediction : Bool

canonicalTransportedAssociatorSupportBoundary :
  TransportedAssociatorSupportBoundary
canonicalTransportedAssociatorSupportBoundary =
  transported-associator-support-boundary
    true true true true true true false false false
