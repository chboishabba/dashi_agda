module DASHI.Physics.ExoticGravity.AntigravityEmpiricalTheoryDiligenceBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.ExoticGravity.AntigravityJointProofSearchFrontierExact as Joint
import DASHI.Physics.ExoticGravity.AntigravityFirstIrreducibleSourceResidualExact as Source
import DASHI.Physics.ExoticGravity.LiTorrTheorySourceDiligenceProofSearchExact as Theory
import DASHI.Physics.ExoticGravity.AntigravityClaimTheoryComparisonExact as Comparison

------------------------------------------------------------------------
-- EMPIRICAL ACQUISITION <-> THEORY-SOURCE DILIGENCE
--
-- Both lanes are live, but they pay different consumers.  Source diligence can
-- make an imported theory claim admissible; it cannot construct the physical
-- source/geometry receipt.  Apparatus measurement can pay the empirical lane;
-- it cannot invent bibliographic or source-entitlement metadata.
------------------------------------------------------------------------

data ProofSearchLane : Set where
  empiricalApparatusLane : ProofSearchLane
  importedTheoryDiligenceLane : ProofSearchLane
  attributedComparisonLane : ProofSearchLane

data LaneStatus : Set where
  liveFirstCut : LaneStatus
  liveParallelResidual : LaneStatus
  blockedUntilInputsPaid : LaneStatus

currentEmpiricalLaneStatus : LaneStatus
currentEmpiricalLaneStatus = liveFirstCut

currentTheoryDiligenceStatus : LaneStatus
currentTheoryDiligenceStatus = liveParallelResidual

currentComparisonStatus : LaneStatus
currentComparisonStatus = blockedUntilInputsPaid

currentEmpiricalBundleExact :
  Joint.currentRecommendedBundle ≡ Joint.sourceGeometryBundle
currentEmpiricalBundleExact = refl

currentLiteralShapeResidualExact :
  Source.currentLiteralGeometryFirstOpen
    ≡ Source.currentLiteralGeometryFirstOpen
currentLiteralShapeResidualExact = refl

------------------------------------------------------------------------
-- No cross-payment authority is supplied.
------------------------------------------------------------------------

data TheoryDiligencePaysEmpiricalAuthority : Set where

data EmpiricalMeasurementPaysTheoryDiligenceAuthority : Set where

theoryDiligenceCannotCreateSourceAcquisitionTarget :
  TheoryDiligencePaysEmpiricalAuthority → Source.SourceAcquisitionTarget
theoryDiligenceCannotCreateSourceAcquisitionTarget ()

empiricalMeasurementCannotCreateTheorySourceCandidate :
  EmpiricalMeasurementPaysTheoryDiligenceAuthority → Theory.LiTorrTheorySourceCandidate
empiricalMeasurementCannotCreateTheorySourceCandidate ()

------------------------------------------------------------------------
-- The two lanes meet only at the comparison consumer, where both a calibrated
-- claim-bound observation and an attributed prediction are required.
------------------------------------------------------------------------

record ComparisonEntryBoundary : Set where
  constructor comparison-entry-boundary
  field
    apparatusClosureNeededForMeasurementSide : Bool
    theoryDiligenceNeededForExternalPredictionSide : Bool
    eitherLaneAloneMayEnterAttributedComparison : Bool
    payingTheoryDiligenceCountsAsExperimentalProgress : Bool
    payingEmpiricalSourceBundleCompletesTheoryAttribution : Bool
    bothLanesMayConvergeAtComparison : Bool

canonicalComparisonEntryBoundary : ComparisonEntryBoundary
canonicalComparisonEntryBoundary =
  comparison-entry-boundary true true false false false true

record EmpiricalTheoryDiligenceBoundary : Set where
  constructor empirical-theory-diligence-boundary
  field
    physicalSourceAndTheorySourceAreSameCoordinate : Bool
    theorySourceSearchMayProceedInParallel : Bool
    empiricalSourceAcquisitionRemainsHighestAlphaPhysicalMove : Bool
    importedTheoryMaySkipAttributionBecauseExperimentIsInteresting : Bool
    completedDiligenceAutomaticallyValidatesLiTorrPhysics : Bool

canonicalEmpiricalTheoryDiligenceBoundary : EmpiricalTheoryDiligenceBoundary
canonicalEmpiricalTheoryDiligenceBoundary =
  empirical-theory-diligence-boundary false true true false false
