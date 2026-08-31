module DASHI.SexedHistoricalReopenableSynthesisValidation where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.EpistemicSuspensionExact as Suspension
import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Governance.SexedHistoricalProductiveDialecticalFibreJoinExact as Join
import DASHI.Governance.SexedHistoricalDialecticalJoinAdaptiveSearchExact as Search
import DASHI.Governance.SexedHistoricalReopenableSynthesisEndOfHistoryBoundaryExact as Reopen
import DASHI.Governance.SexedHistoricalSelectiveReopeningExact as Selective
import DASHI.Governance.SexedHistoricalBracketedMultiverseTSFVBridgeExact as Bracketed
import DASHI.Governance.SexedHistoricalStratifiedCollectiveGluingExact as Gluing
import DASHI.Governance.SexedHistoricalDistributedCompatibilityReopeningExact as Distributed
import DASHI.Governance.SexedHistoricalCoalitionAssociatorYijingExact as Associator

productiveJoinNextHistoryRegression :
  INF.FactorsThrough Reopen.joinPresentSurface Reopen.nextContinuation → ⊥
productiveJoinNextHistoryRegression =
  Reopen.productiveJoinSurfaceCannotRecoverNextHistory

productiveJoinHasOutgoingTransitionRegression :
  Reopen.JoinTransport Reopen.productiveJoinAtT Reopen.counterformationAtNext
productiveJoinHasOutgoingTransitionRegression =
  Reopen.canonicalJoinHasOutgoingTransport

productiveJoinAcceptedNowRegression :
  Join.joinDisposition Join.productiveJoin ≡ Suspension.acceptHere
productiveJoinAcceptedNowRegression = Reopen.currentJoinAcceptedAsProductive

historicalFinalityStillOpenRegression :
  Reopen.finalityDisposition Reopen.finalityUnresolved
  ≡ Suspension.suspendAndRefine
historicalFinalityStillOpenRegression =
  Reopen.historicalFinalityRemainsUnresolvedInCanonicalFixture

selectivePowerGateReopeningRegression :
  Dependency.ReopeningObligation
    Selective.Depends
    Selective.counterformationResidual
    Selective.powerGateCertificate
selectivePowerGateReopeningRegression = Selective.powerGateMustReopen

selectiveNextJoinSearchReopeningRegression :
  Dependency.ReopeningObligation
    Selective.Depends
    Selective.counterformationResidual
    Selective.nextJoinSearchCertificate
selectiveNextJoinSearchReopeningRegression = Selective.nextJoinSearchMustReopen

reopenedSearchMeasurementRegression :
  Search.nextJoinMeasurement
    Search.verifyStrictAffordanceExpansion
    (Join.joinDisposition Join.unresolvedJoin)
  ≡ Search.optionConeProbe
reopenedSearchMeasurementRegression =
  Selective.reopenedJoinSearchSelectsAffordanceProbe

bracketingChangesEffectiveRepairRegression :
  Bracketed.leftBracketedRepair ≡ Bracketed.rightBracketedRepair → ⊥
bracketingChangesEffectiveRepairRegression =
  Bracketed.bracketingChangesEffectiveRepair

sameResidualInventoryOutcomeRegression :
  INF.FactorsThrough
    Bracketed.residualInventory Bracketed.bracketedOutcome → ⊥
sameResidualInventoryOutcomeRegression =
  Bracketed.sameInventoryCannotRecoverBracketedOutcome

samePresentDescendantFutureRegression :
  INF.FactorsThrough
    Bracketed.coarsePresent Bracketed.branchFutureCone → ⊥
samePresentDescendantFutureRegression =
  Bracketed.samePresentCannotRecoverDescendantFuture

branchFutureProbeRegression :
  Bracketed.measureBranch
    (Bracketed.nextBranchMeasurement
      Bracketed.recoverFutureCone Suspension.suspendAndRefine)
    Bracketed.reciprocalExpansionBranch
  ≡ Bracketed.measureBranch
    (Bracketed.nextBranchMeasurement
      Bracketed.recoverFutureCone Suspension.suspendAndRefine)
    Bracketed.counterformationBranch → ⊥
branchFutureProbeRegression =
  Bracketed.selectedFutureProbeSeparatesCanonicalBranches

canonicalTwoBoundaryCorridorRegression :
  Bracketed.TwoBoundaryDescendantFibre
    Bracketed.inheritedProductiveJoinHistory
    Bracketed.preserveReciprocity
canonicalTwoBoundaryCorridorRegression = Bracketed.canonicalReciprocalCorridor

stratumCannotRecoverLocalBranchRegression :
  INF.FactorsThrough
    Gluing.feminineStratumSurface Gluing.feminineContinuationSurface → ⊥
stratumCannotRecoverLocalBranchRegression =
  Gluing.stratumCannotRecoverLocalContinuation

globalSurfaceCannotRecoverLocalIntegrityRegression :
  INF.FactorsThrough Gluing.globalPublicSurface Gluing.globalIntegrity → ⊥
globalSurfaceCannotRecoverLocalIntegrityRegression =
  Gluing.globalSurfaceCannotRecoverLocalIntegrity

blockedFamilyIsLocallyLiveRegression :
  Gluing.AllLocallyLive Gluing.blockedCollectiveFamily
blockedFamilyIsLocallyLiveRegression =
  Gluing.blockedCollectiveFamilyLocallyLive

blockedFamilyStillCannotGlueRegression :
  Gluing.CompatibleFamily Gluing.blockedCollectiveFamily → ⊥
blockedFamilyStillCannotGlueRegression =
  Gluing.blockedCollectiveFamilyCannotGlue

minimalCompatibilityExtensionRegression : Gluing.MinimalCompatibilityExtension
minimalCompatibilityExtensionRegression =
  Gluing.canonicalMinimalCompatibilityExtension

distributedGlobalCompatibilityReopeningRegression :
  Dependency.ReopeningObligation
    Distributed.Depends
    Distributed.feminineEnactedBranch
    Distributed.globalCompatibilityCertificate
distributedGlobalCompatibilityReopeningRegression =
  Distributed.globalCompatibilityMustReopenFromFeminineEnactment

distributedCollectiveFutureReopeningRegression :
  Dependency.ReopeningObligation
    Distributed.Depends
    Distributed.feminineEnactedBranch
    Distributed.collectiveFutureConeCertificate
distributedCollectiveFutureReopeningRegression =
  Distributed.collectiveFutureConeMustReopenFromFeminineEnactment

coalitionAssociatorDefectRegression :
  Associator.leftBracketedGlobal ≡ Associator.rightBracketedGlobal → ⊥
coalitionAssociatorDefectRegression = Associator.coalitionAssociatorDefect

sameParticipantsCoalitionOutcomeRegression :
  INF.FactorsThrough
    Associator.participantInventory Associator.coalitionOutcome → ⊥
sameParticipantsCoalitionOutcomeRegression =
  Associator.sameParticipantsCannotRecoverCoalitionOutcome

yijingBracketSignatureRegression :
  Associator.leftBracketSignature ≡ Associator.rightBracketSignature → ⊥
yijingBracketSignatureRegression =
  Associator.coalitionBracketProducesDifferentRelationalSignature

coalitionAssociatorResidualRegression :
  Associator.CoalitionAssociatorResidual
    Associator.leftBracketedGlobal Associator.rightBracketedGlobal
coalitionAssociatorResidualRegression =
  Associator.canonicalCoalitionAssociator

selectiveReopeningBoundaryRegression :
  Selective.SelectiveHistoricalReopeningBoundary
selectiveReopeningBoundaryRegression =
  Selective.canonicalSelectiveHistoricalReopeningBoundary

bracketedMultiverseTSFVBoundaryRegression :
  Bracketed.BracketedMultiverseTSFVBoundary
bracketedMultiverseTSFVBoundaryRegression =
  Bracketed.canonicalBracketedMultiverseTSFVBoundary

stratifiedCollectiveGluingBoundaryRegression :
  Gluing.StratifiedCollectiveGluingBoundary
stratifiedCollectiveGluingBoundaryRegression =
  Gluing.canonicalStratifiedCollectiveGluingBoundary

distributedCompatibilityReopeningBoundaryRegression :
  Distributed.DistributedCompatibilityReopeningBoundary
distributedCompatibilityReopeningBoundaryRegression =
  Distributed.canonicalDistributedCompatibilityReopeningBoundary

coalitionAssociatorYijingBoundaryRegression :
  Associator.CoalitionAssociatorYijingBoundary
coalitionAssociatorYijingBoundaryRegression =
  Associator.canonicalCoalitionAssociatorYijingBoundary

canonicalSourceBoundaryRegression :
  Reopen.ReopenableSynthesisEndOfHistoryBoundary
canonicalSourceBoundaryRegression =
  Reopen.canonicalReopenableSynthesisEndOfHistoryBoundary
