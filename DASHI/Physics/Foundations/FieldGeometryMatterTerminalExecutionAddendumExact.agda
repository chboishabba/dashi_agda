module DASHI.Physics.Foundations.FieldGeometryMatterTerminalExecutionAddendumExact where

open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.Foundations.FieldGeometryMatterTerminalMaxCutExact as Terminal
import DASHI.Physics.CondensedMatter.MATBGTHFSelfConsistencyObstructionReceiptExact as THFObstruction
import DASHI.Physics.CondensedMatter.MATBG2026SourceDataAvailabilityExact as SourceData
import DASHI.Physics.Foundations.ScientistFrontierSiblingHandoffExact as ScientistHandoff

record TerminalExecutionAddendum : Set where
  constructor terminal-execution-addendum
  field
    thfFiniteQuadratureObstructionReplay : Terminal.FrontierStatus
    thfSourceFaithfulSelfConsistentSolve : Terminal.FrontierStatus
    thfBZNormalizationAndCutoffProducer : Terminal.FrontierStatus
    thfVYNotationResolution : Terminal.FrontierStatus
    qtmSourceDataAvailability : Terminal.FrontierStatus
    entropySourceDataAvailability : Terminal.FrontierStatus
    qtmSourceDataBytes : Terminal.FrontierStatus
    entropySourceDataBytes : Terminal.FrontierStatus
    crossStudySameSampleIdentity : Terminal.FrontierStatus
    scientistFrontierDedicatedAcquisitionOwner : Terminal.FrontierStatus
    scientistFrontierCrossObjectPromotion : Terminal.FrontierStatus
    obstructionReplayCountsAsSolvedTHF : Bool
    sourceDataAvailabilityCountsAsReplay : Bool
    scientistTechnicalAdjacencyCountsAsTargeting : Bool

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
    Terminal.openSameObjectPayment
    Terminal.openSameObjectPayment
    Terminal.externalOnly
    Terminal.blockedByUnmergedSibling
    Terminal.openSameObjectPayment
    false false false

record TerminalExecutionAddendumBoundary : Set where
  constructor terminal-execution-addendum-boundary
  field
    obstructionReceiptImported : THFObstruction.THFSelfConsistencyObstructionBoundary
    sourceDataBoundaryImported : SourceData.MATBGSourceDataAvailabilityBoundary
    scientistHandoffBoundaryImported : ScientistHandoff.ScientistFrontierHandoffBoundary
    noGenericAbstractionPromotesRemainingLeaves : Bool

open TerminalExecutionAddendumBoundary public

canonicalTerminalExecutionAddendumBoundary : TerminalExecutionAddendumBoundary
canonicalTerminalExecutionAddendumBoundary =
  terminal-execution-addendum-boundary
    THFObstruction.canonicalTHFSelfConsistencyObstructionBoundary
    SourceData.canonicalMATBGSourceDataAvailabilityBoundary
    ScientistHandoff.canonicalScientistFrontierHandoffBoundary
    true
