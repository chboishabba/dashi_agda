module DASHI.Governance.SexedHistoricalCollectiveThresholdNetworkExact where

------------------------------------------------------------------------
-- COLLECTIVE ENACTMENT / THRESHOLD / NETWORK EFFECTS
--
-- Cross-pollinates the enacted-choice feedback hyperfabric with the generic
-- threshold/residual geometry and the revolutionary-practice braid.
--
-- Central separation:
--
--   individual enactment != collective threshold crossing
--   threshold crossing != institutional victory
--   public legibility != power parity
--   collective memory != unbroken institutional continuity
--
-- The historical application constructors below are comparison vocabulary only.
-- They do not assert that suffrage, abolition, Luddism, apostasy communities,
-- covens or counter-movements share one doctrine, causal mechanism or outcome.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.ThresholdResidualTrajectoryGeometryExact as Threshold
import DASHI.Governance.SexedHistoricalActionFeedbackHyperfabricExact as Feedback
import DASHI.Governance.SexedHistoricalChoiceConeBridgeExact as Choice
import DASHI.Governance.RevolutionaryPracticeBraid as Practice

------------------------------------------------------------------------
-- Collective-action surface.
------------------------------------------------------------------------

data CollectiveActionKind : Set where
  suffrageMobilisation
  abolitionMobilisation
  ludditeCollectiveResistance
  religiousExitCommunity
  feministWitchCollective
  masculineCounterMovement
  crossSexSolidarityNetwork
  : CollectiveActionKind

data ParticipationBand : Set where
  isolatedParticipation
  emergingCollective
  thresholdCollective
  massCollective
  : ParticipationBand

data PublicLegibility : Set where
  privatelyLegible
  locallyLegible
  publiclyLegible
  institutionallyLegible
  : PublicLegibility

data CoordinationCapacity : Set where
  fragmentedCoordination
  localCoordination
  networkedCoordination
  durableCoordination
  : CoordinationCapacity

data MemoryStatus : Set where
  ephemeralMemory
  retainedMemory
  transmittedMemory
  contestedMemory
  : MemoryStatus

data CollectiveOutcome : Set where
  noInstitutionalShift
  partialInstitutionalShift
  institutionalShift
  counterMobilisation
  : CollectiveOutcome

record CollectiveActionState : Set where
  constructor collective-action-state
  field
    actionKind : CollectiveActionKind
    participation : ParticipationBand
    legibility : PublicLegibility
    coordination : CoordinationCapacity
    memory : MemoryStatus
    downstreamOutcome : CollectiveOutcome
    otherSubjectOption : Choice.ConceivedChoiceSurface

open CollectiveActionState public

------------------------------------------------------------------------
-- Threshold geometry is reused as geometry only.  A threshold observation does
-- not itself supply historical semantics or institutional success.
------------------------------------------------------------------------

emergingParticipationThreshold : Threshold.ThresholdObservation
emergingParticipationThreshold =
  Threshold.thresholdObservation Threshold.higherIsBetter 3 2

crossedParticipationThreshold : Threshold.ThresholdObservation
crossedParticipationThreshold =
  Threshold.thresholdObservation Threshold.higherIsBetter 3 3

emergingBelowThreshold :
  Threshold.withinThreshold emergingParticipationThreshold ≡ false
emergingBelowThreshold = refl

collectiveAtThreshold :
  Threshold.withinThreshold crossedParticipationThreshold ≡ true
collectiveAtThreshold = refl

thresholdGeometryRetainsResidualMagnitudeBoundary :
  Threshold.ThresholdTrajectoryBoundary.thresholdStatusDeterminesResidualMagnitude
    Threshold.canonicalThresholdTrajectoryBoundary
  ≡ false
thresholdGeometryRetainsResidualMagnitudeBoundary =
  Threshold.ThresholdTrajectoryBoundary.thresholdStatusDeterminesResidualMagnitudeIsFalse
    Threshold.canonicalThresholdTrajectoryBoundary

------------------------------------------------------------------------
-- Threshold crossing can make an option publicly legible in a finite specimen,
-- but that is not promoted to a universal social law.
------------------------------------------------------------------------

preThresholdState : CollectiveActionState
preThresholdState =
  collective-action-state
    suffrageMobilisation
    emergingCollective
    locallyLegible
    localCoordination
    retainedMemory
    noInstitutionalShift
    Choice.notConceived

postThresholdLegibilityState : CollectiveActionState
postThresholdLegibilityState =
  collective-action-state
    suffrageMobilisation
    thresholdCollective
    publiclyLegible
    networkedCoordination
    transmittedMemory
    partialInstitutionalShift
    Choice.conceivedAsPossible

------------------------------------------------------------------------
-- More participation / threshold status does not determine institutional
-- outcome.  Two threshold-crossed states share the same participation surface
-- but differ in institutional reception.
------------------------------------------------------------------------

data ThresholdOutcomeFineState : Set where
  thresholdWithShift
  thresholdWithCounterMobilisation
  : ThresholdOutcomeFineState

participationSurface : ThresholdOutcomeFineState → ParticipationBand
participationSurface _ = thresholdCollective

institutionalOutcome : ThresholdOutcomeFineState → CollectiveOutcome
institutionalOutcome thresholdWithShift = institutionalShift
institutionalOutcome thresholdWithCounterMobilisation = counterMobilisation

participationCannotRecoverInstitutionalOutcome :
  INF.FactorsThrough participationSurface institutionalOutcome → ⊥
participationCannotRecoverInstitutionalOutcome =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      thresholdWithShift
      thresholdWithCounterMobilisation
      refl
      (λ ()))

------------------------------------------------------------------------
-- Public legibility likewise does not determine power outcome.
------------------------------------------------------------------------

publicLegibilitySurface : ThresholdOutcomeFineState → PublicLegibility
publicLegibilitySurface _ = publiclyLegible

publicLegibilityCannotRecoverInstitutionalOutcome :
  INF.FactorsThrough publicLegibilitySurface institutionalOutcome → ⊥
publicLegibilityCannotRecoverInstitutionalOutcome =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      thresholdWithShift
      thresholdWithCounterMobilisation
      refl
      (λ ()))

------------------------------------------------------------------------
-- Network effects on another subject's conceived option are separately typed.
-- The same public action category may coexist with different option effects.
------------------------------------------------------------------------

data NetworkOptionFineState : Set where
  visibleNetworkWithoutOptionExpansion
  visibleNetworkWithOptionExpansion
  : NetworkOptionFineState

networkActionSurface : NetworkOptionFineState → Feedback.EnactedAction
networkActionSurface _ = Feedback.crossSexSolidarity

otherSubjectConceivedOption :
  NetworkOptionFineState → Choice.ConceivedChoiceSurface
otherSubjectConceivedOption visibleNetworkWithoutOptionExpansion = Choice.notConceived
otherSubjectConceivedOption visibleNetworkWithOptionExpansion = Choice.conceivedAsPossible

sameNetworkActionCannotRecoverOtherSubjectOption :
  INF.FactorsThrough networkActionSurface otherSubjectConceivedOption → ⊥
sameNetworkActionCannotRecoverOtherSubjectOption =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      visibleNetworkWithoutOptionExpansion
      visibleNetworkWithOptionExpansion
      refl
      (λ ()))

------------------------------------------------------------------------
-- Memory can transmit action legibility without establishing continuous
-- institutions or identical practitioner lineage.
------------------------------------------------------------------------

data TransmittedMemoryImpliesInstitutionalContinuity : Set where

data PublicLegibilityImpliesPowerParity : Set where

data ThresholdCrossingGuaranteesVictory : Set where

data MoreParticipantsGuaranteeLiberatoryOutcome : Set where

data CollectiveActionGuaranteesUniformSubjectFormation : Set where

data CounterMovementRestoresIdenticalPriorOrder : Set where

transmittedMemoryDoesNotImplyInstitutionalContinuity :
  TransmittedMemoryImpliesInstitutionalContinuity → ⊥
transmittedMemoryDoesNotImplyInstitutionalContinuity ()

publicLegibilityDoesNotImplyPowerParity :
  PublicLegibilityImpliesPowerParity → ⊥
publicLegibilityDoesNotImplyPowerParity ()

thresholdCrossingDoesNotGuaranteeVictory :
  ThresholdCrossingGuaranteesVictory → ⊥
thresholdCrossingDoesNotGuaranteeVictory ()

moreParticipantsDoNotGuaranteeLiberatoryOutcome :
  MoreParticipantsGuaranteeLiberatoryOutcome → ⊥
moreParticipantsDoNotGuaranteeLiberatoryOutcome ()

collectiveActionDoesNotGuaranteeUniformSubjectFormation :
  CollectiveActionGuaranteesUniformSubjectFormation → ⊥
collectiveActionDoesNotGuaranteeUniformSubjectFormation ()

counterMovementDoesNotRestoreIdenticalPriorOrder :
  CounterMovementRestoresIdenticalPriorOrder → ⊥
counterMovementDoesNotRestoreIdenticalPriorOrder ()

------------------------------------------------------------------------
-- Practice-braid cross-pollination: unity/coordination does not require
-- doctrinal uniformity, and institutional change remains distinct from
-- relational change.
------------------------------------------------------------------------

collectiveUnityDoesNotRequireUniformity :
  Practice.unityRequiresUniformity
    Practice.canonicalRevolutionaryPracticeBraidSurface
  ≡ false
collectiveUnityDoesNotRequireUniformity =
  Practice.RevolutionaryPracticeBraidBoundary.unityDoesNotRequireUniformity
    Practice.canonicalRevolutionaryPracticeBraidBoundary

collectiveInstitutionalChangeDoesNotCloseRelationalChange :
  Practice.institutionalChangeImpliesRelationalChange
    Practice.canonicalRevolutionaryPracticeBraidSurface
  ≡ false
collectiveInstitutionalChangeDoesNotCloseRelationalChange =
  Practice.RevolutionaryPracticeBraidBoundary.institutionalChangeDoesNotCloseRelationalChange
    Practice.canonicalRevolutionaryPracticeBraidBoundary

------------------------------------------------------------------------
-- Boundary surface.
------------------------------------------------------------------------

record SexedHistoricalCollectiveThresholdBoundary : Set where
  constructor sexed-historical-collective-threshold-boundary
  field
    individualActionEqualsCollectiveThreshold : Bool
    thresholdCrossingGuaranteesInstitutionalVictory : Bool
    moreParticipantsGuaranteeLiberatoryOutcome : Bool
    publicLegibilityEqualsPowerParity : Bool
    transmittedMemoryEqualsInstitutionalContinuity : Bool
    collectiveActionUniformlyRewritesSubjects : Bool
    counterMovementRestoresIdenticalPast : Bool
    collectiveEffectsRemainReceptionIndexed : Bool
    thresholdResidualMagnitudeRemainsSeparate : Bool
    coordinationNeedNotMeanUniformity : Bool

canonicalSexedHistoricalCollectiveThresholdBoundary :
  SexedHistoricalCollectiveThresholdBoundary
canonicalSexedHistoricalCollectiveThresholdBoundary =
  sexed-historical-collective-threshold-boundary
    false false false false false false false true true true
