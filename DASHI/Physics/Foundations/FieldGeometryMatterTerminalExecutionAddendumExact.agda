module DASHI.Physics.Foundations.FieldGeometryMatterTerminalExecutionAddendumExact where

open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.Foundations.FieldGeometryMatterTerminalMaxCutExact as Terminal
import DASHI.Physics.CondensedMatter.MATBGTHFSelfConsistencyObstructionReceiptExact as THFObstruction
import DASHI.Physics.CondensedMatter.MATBG2026SourceDataAvailabilityExact as SourceData
import DASHI.Physics.CondensedMatter.MATBGEntropyMaxwellReplayContractExact as EntropyMaxwell
import DASHI.Physics.Foundations.ScientistFrontierSiblingHandoffExact as ScientistHandoff
import DASHI.Physics.Foundations.FieldGeometryMatterSiblingAuthorityHandoffExact as SiblingHandoff

record TerminalExecutionAddendum : Set where
  constructor terminal-execution-addendum
  field
    thfFiniteQuadratureObstructionReplay : Terminal.FrontierStatus
    thfSourceFaithfulSelfConsistentSolve : Terminal.FrontierStatus
    thfBZNormalizationAndCutoffProducer : Terminal.FrontierStatus
    thfVYNotationResolution : Terminal.FrontierStatus
    qtmSourceDataAvailability : Terminal.FrontierStatus
    entropySourceDataAvailability : Terminal.FrontierStatus
    entropyMaxwellReplayKernel : Terminal.FrontierStatus
    qtmSourceDataBytes : Terminal.FrontierStatus
    entropySourceDataBytes : Terminal.FrontierStatus
    crossStudySameSampleIdentity : Terminal.FrontierStatus
    scientistFrontierDedicatedAcquisitionOwner : Terminal.FrontierStatus
    scientistFrontierCrossObjectPromotion : Terminal.FrontierStatus
    magnetocaloricDedicatedSiblingOwner : Terminal.FrontierStatus
    fusionPropulsionDedicatedSiblingOwner : Terminal.FrontierStatus
    rocketdyneDedicatedSiblingOwner : Terminal.FrontierStatus
    obstructionReplayCountsAsSolvedTHF : Bool
    sourceDataAvailabilityCountsAsReplay : Bool
    entropyMaxwellSyntheticFixtureCountsAsMeasuredReplay : Bool
    scientistTechnicalAdjacencyCountsAsTargeting : Bool
    openSiblingReferenceCountsAsAuthorityImport : Bool

open TerminalExecutionAddendum public

currentTerminalExecutionAddendum : TerminalExecutionAddendum
currentTerminalExecutionAddendum =
  terminal-execution-addendum
    Terminal.numericallyExecuted
    Terminal.openCalibrationOrExecution
    Terminal.openSameObjectPayment
    Terminal.openSameObjectPayment
    Terminal.sourcePaid
    Terminal.sourcePaid
    Terminal.numericallyExecuted
    Terminal.openSameObjectPayment
    Terminal.openSameObjectPayment
    Terminal.externalOnly
    Terminal.blockedByUnmergedSibling
    Terminal.openSameObjectPayment
    Terminal.blockedByUnmergedSibling
    Terminal.blockedByUnmergedSibling
    Terminal.blockedByUnmergedSibling
    false false false false false

record TerminalExecutionAddendumBoundary : Set where
  constructor terminal-execution-addendum-boundary
  field
    obstructionReceiptImported : THFObstruction.THFSelfConsistencyObstructionBoundary
    sourceDataBoundaryImported : SourceData.MATBGSourceDataAvailabilityBoundary
    entropyMaxwellBoundaryImported : EntropyMaxwell.EntropyMaxwellReplayBoundary
    scientistHandoffBoundaryImported : ScientistHandoff.ScientistFrontierHandoffBoundary
    siblingAuthorityHandoffBoundaryImported : SiblingHandoff.SiblingAuthorityHandoffBoundary
    noGenericAbstractionPromotesRemainingLeaves : Bool

open TerminalExecutionAddendumBoundary public

canonicalTerminalExecutionAddendumBoundary : TerminalExecutionAddendumBoundary
canonicalTerminalExecutionAddendumBoundary =
  terminal-execution-addendum-boundary
    THFObstruction.canonicalTHFSelfConsistencyObstructionBoundary
    SourceData.canonicalMATBGSourceDataAvailabilityBoundary
    EntropyMaxwell.canonicalEntropyMaxwellReplayBoundary
    ScientistHandoff.canonicalScientistFrontierHandoffBoundary
    SiblingHandoff.canonicalSiblingAuthorityHandoffBoundary
    true
