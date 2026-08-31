module DASHI.SexedHistoricalTransportedSupportValidation where

open import DASHI.Core.Prelude

import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Core.DiscriminatorSynthesisExact as Discriminator
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.SexedHistoricalAssociatorSupportedReopeningExact as Supported
import DASHI.Governance.SexedHistoricalDistributedCompatibilityReopeningExact as Distributed
import DASHI.Governance.SexedHistoricalTransportedAssociatorSupportExact as Transported
import DASHI.Governance.SexedHistoricalTransportedSupportDiscriminatorExact as SupportDiscriminator

canonicalSupportHistoryRegression :
  Transported.SupportTransportPath
    Transported.initialAssociatorStage
    Transported.institutionalPersistenceStage
canonicalSupportHistoryRegression = Transported.canonicalSupportHistory

initialSupportLine1Regression :
  Transported.ActiveAt Transported.initialAssociatorStage Supported.line1
initialSupportLine1Regression = Transported.initialLine1

localRepairDischargesLine1Regression :
  Transported.ActiveAt Transported.localRepairStage Supported.line1 → ⊥
localRepairDischargesLine1Regression = Transported.line1DischargedByLocalRepair

counterformationActivatesLine5Regression :
  Transported.ActiveAt Transported.networkCounterformationStage Supported.line5
counterformationActivatesLine5Regression =
  Transported.line5ActivatedByCounterformation

counterformationLine5ReopensFutureRegression :
  Dependency.ReopeningObligation
    Distributed.Depends
    (Transported.stageArtifact
      Transported.networkCounterformationStage Supported.line5)
    Distributed.collectiveFutureConeCertificate
counterformationLine5ReopensFutureRegression =
  Transported.counterformationLine5ReopensCollectiveFuture

sameCoarseSupportHistoryRegression :
  INF.FactorsThrough
    Transported.coarseSupportSurface Transported.fineSupportHistoryCode → ⊥
sameCoarseSupportHistoryRegression =
  Transported.sameCoarseSupportCannotRecoverSupportHistory

supportHistoryCollisionRegression :
  Discriminator.CurrentObserverCollision Transported.coarseSupportSurface
supportHistoryCollisionRegression =
  SupportDiscriminator.supportHistoryCollision

supportOrderSeparatorRegression :
  Discriminator.BundleSeparates
    SupportDiscriminator.supportOrderProbe
    Transported.repairedThenCounterformed
    Transported.counterformedThenRepaired
supportOrderSeparatorRegression =
  SupportDiscriminator.supportOrderProbeSeparates

joinedSupportObserverSeparatesRegression :
  Discriminator.joinedObservation
    Transported.coarseSupportSurface SupportDiscriminator.supportOrderProbe
    Transported.repairedThenCounterformed
  ≡ Discriminator.joinedObservation
    Transported.coarseSupportSurface SupportDiscriminator.supportOrderProbe
    Transported.counterformedThenRepaired → ⊥
joinedSupportObserverSeparatesRegression =
  SupportDiscriminator.joinedObserverSeparatesSupportHistories

transportedSupportBoundaryRegression :
  Transported.TransportedAssociatorSupportBoundary
transportedSupportBoundaryRegression =
  Transported.canonicalTransportedAssociatorSupportBoundary

supportDiscriminatorBoundaryRegression :
  SupportDiscriminator.TransportedSupportDiscriminatorBoundary
supportDiscriminatorBoundaryRegression =
  SupportDiscriminator.canonicalTransportedSupportDiscriminatorBoundary
