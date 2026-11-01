module DASHI.Biology.BioacousticMultimodalEpisodeTrajectoryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.BioacousticAnimalexicTrajectoryBridgeExact as ABI
import DASHI.Biology.BioacousticSituatedPerformanceEnergyExact as Situated

------------------------------------------------------------------------
-- SAME-EPISODE MULTIMODAL TRAJECTORY
--
-- Thin composition over the existing Animalexic governed-trajectory ABI and
-- the situated birdsong-performance carrier.  Each modality retains its own
-- source clock/reference; a common episode coordinate may be asserted only by
-- an explicit alignment receipt.  Clock alignment is synchronization, not
-- causality, mechanism, identity promotion or canonical-state promotion.
------------------------------------------------------------------------

record MultimodalEpisodeClockReceipt : Set where
  constructor multimodal-episode-clock-receipt
  field
    episodeIdentity : String
    episodeStartReference : String
    episodeEndReference : String
    acousticTimeReference : String
    respiratoryTimeReference : String
    cardiacTimeReference : String
    movementTimeReference : String
    energeticTimeReference : String
    contextTimeReference : String
    alignmentMethodReference : String
    alignmentResidualReference : String
    sameEpisodeIdentityRequired : Bool
    sourceClocksRetained : Bool
    alignmentResidualRetained : Bool
    clockAlignmentDoesNotCreateCausality : Bool
    clockAlignmentDoesNotCreateMechanism : Bool
    clockAlignmentDoesNotCreateCrossModalIdentity : Bool

open MultimodalEpisodeClockReceipt public

record MultimodalEpisodeSample : Set where
  constructor multimodal-episode-sample
  field
    episodeTime : String
    situatedState : Situated.SituatedPerformanceState
    clockReceipt : MultimodalEpisodeClockReceipt
    acousticProvenance : String
    respiratoryProvenance : String
    cardiacProvenance : String
    movementProvenance : String
    energeticProvenance : String
    decision : ABI.RuntimeDecision
    residual : String
    receiptIdentity : String

open MultimodalEpisodeSample public

------------------------------------------------------------------------
-- Existing runtime ABI is reused rather than replaced.  A runtime projection
-- may emit one governed row per selected modality/channel at the shared episode
-- coordinate while retaining modality-specific provenance in each row.
------------------------------------------------------------------------

trajectoryABISchemaReused : String
trajectoryABISchemaReused = "animalexic-state-space-trajectory-v1"

multimodalChannelNames : List String
multimodalChannelNames =
  "acoustic" ∷
  "respiratory" ∷
  "cardiac" ∷
  "movement" ∷
  "metabolic-power" ∷
  "acoustic-power" ∷
  "accumulated-energy" ∷
  "situated-context" ∷ []

record MultimodalTrajectoryBoundary : Set where
  constructor multimodal-trajectory-boundary
  field
    alignedTimestampMeansSameSensorClock : Bool
    alignedTimestampMeansSamePhysicalMechanism : Bool
    crossModalCorrelationMeansCausality : Bool
    acousticLeadMeansNeuralOrMotorCause : Bool
    heartRateLeadMeansEnergeticCause : Bool
    movementCoincidenceMeansVocalMechanism : Bool
    missingModalityMayBeImputedAsObserved : Bool
    promotionRemainsUpstream : Bool
    receiptIdentityRemainsVisible : Bool
    provenanceRemainsPerChannel : Bool
    sameEpisodeIdentityMustBePaid : Bool

open MultimodalTrajectoryBoundary public

canonicalMultimodalTrajectoryBoundary : MultimodalTrajectoryBoundary
canonicalMultimodalTrajectoryBoundary = multimodal-trajectory-boundary
  false false false false false false false true true true true

------------------------------------------------------------------------
-- Bidi reopening: a synchronized episode remains valid only for the modalities
-- whose source-time mapping and same-episode identity stay paid.  A later clock
-- correction reopens only the affected synchronization dependency; it does not
-- erase source observations or promote causal claims.
------------------------------------------------------------------------

record MultimodalBidiReceipt : Set where
  constructor multimodal-bidi-receipt
  field
    forwardAlignmentClaim : String
    reverseReopeningCondition : String
    reopenedDependency : String
    sourceObservationsRetained : Bool
    historicalAlignmentReceiptRetained : Bool
    causalInterpretationStillSeparate : Bool

open MultimodalBidiReceipt public

canonicalMultimodalBidiReceipt : MultimodalBidiReceipt
canonicalMultimodalBidiReceipt = multimodal-bidi-receipt
  "source-bound modality clocks may be mapped to one episode coordinate when an explicit same-episode alignment receipt exists"
  "clock drift, revised trigger/frame mapping, changed trial identity, missing modality timing, or failed residual bound"
  "only the affected modality-to-episode time map and dependent synchronized consumers"
  true true true

sameEpisodeReading : String
sameEpisodeReading =
  "A multimodal birdsong trajectory is a synchronized bundle of acoustic, respiratory, cardiac, movement, energetic and situated-context fibres over one paid episode identity. Alignment permits temporal comparison and lag analysis, but does not manufacture causal direction, mechanism, cross-modal identity, energetic calibration or Animalexic promotion."
