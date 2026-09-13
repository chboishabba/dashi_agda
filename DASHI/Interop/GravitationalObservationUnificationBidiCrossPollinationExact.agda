module DASHI.Interop.GravitationalObservationUnificationBidiCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.GR.GravitationalObservationBidiExact as Obs
import DASHI.Physics.GR.GravitationalWaveTheoryTestBidiExact as Wave
import DASHI.Physics.GR.GravitationalPredictionObservationBidiExact as Pred
import DASHI.Physics.GR.GravitationalMultiScaleTheoryFingerprintBidiExact as Multi
import DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact as Anti
import DASHI.Physics.ExoticGravity.AntigravityUnificationInteractionExact as Unified
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search
import DASHI.Papers.CoreTheoremInterfaces as Core

data CrossPollinationLane : Set where
  observationEvidenceLane grTheoryLane navierStokesConfounderLane
    yangMillsSourceLane riemannMethodLane unificationConsumerLane : CrossPollinationLane

data CrossPollinationRole : Set where
  acquireEvidence compareGravityTheory closeOrdinaryMomentum constrainGaugeSource
    borrowProofDisciplineOnly registerCrossSectorResidual : CrossPollinationRole

roleForLane : CrossPollinationLane → CrossPollinationRole
roleForLane observationEvidenceLane = acquireEvidence
roleForLane grTheoryLane = compareGravityTheory
roleForLane navierStokesConfounderLane = closeOrdinaryMomentum
roleForLane yangMillsSourceLane = constrainGaugeSource
roleForLane riemannMethodLane = borrowProofDisciplineOnly
roleForLane unificationConsumerLane = registerCrossSectorResidual

laneForPredictionResidual : Pred.PredictionObservationResidual → CrossPollinationLane
laneForPredictionResidual Pred.missingTheoryCarrier = grTheoryLane
laneForPredictionResidual Pred.missingPredictionClaimScope = grTheoryLane
laneForPredictionResidual Pred.missingSourceModel = grTheoryLane
laneForPredictionResidual Pred.missingPropagationModel = grTheoryLane
laneForPredictionResidual Pred.missingDetectorResponse = observationEvidenceLane
laneForPredictionResidual Pred.missingPredictionRevision = observationEvidenceLane
laneForPredictionResidual Pred.missingSameChannelReceipt = observationEvidenceLane
laneForPredictionResidual Pred.missingSameObservableReceipt = observationEvidenceLane
laneForPredictionResidual Pred.missingSystematicBudget = observationEvidenceLane
laneForPredictionResidual Pred.missingComparisonMetric = observationEvidenceLane
laneForPredictionResidual Pred.residualRequiresTheoryRevision = unificationConsumerLane

producerForPredictionResidual : Pred.PredictionObservationResidual → Search.ProducerClass
producerForPredictionResidual Pred.missingTheoryCarrier = Search.propositionSourceProducer
producerForPredictionResidual Pred.missingPredictionClaimScope = Search.discriminatorProducer
producerForPredictionResidual Pred.missingSourceModel = Search.propositionSourceProducer
producerForPredictionResidual Pred.missingPropagationModel = Search.propositionSourceProducer
producerForPredictionResidual Pred.missingDetectorResponse = Search.empiricalEvidenceProducer
producerForPredictionResidual Pred.missingPredictionRevision = Search.attributionProducer
producerForPredictionResidual Pred.missingSameChannelReceipt = Search.identityProducer
producerForPredictionResidual Pred.missingSameObservableReceipt = Search.identityProducer
producerForPredictionResidual Pred.missingSystematicBudget = Search.empiricalEvidenceProducer
producerForPredictionResidual Pred.missingComparisonMetric = Search.discriminatorProducer
producerForPredictionResidual Pred.residualRequiresTheoryRevision = Search.contradictionProducer

------------------------------------------------------------------------
-- Reuse the canonical antigravity route instead of maintaining a second total
-- claim->gravity-channel map.  Inertia and propulsion stay outside GR
-- observation and route to their actual downstream consumer lanes.
------------------------------------------------------------------------

observationRouteForAntigravityClaim :
  Anti.AntigravityClaim → Unified.ClaimObservationRoute
observationRouteForAntigravityClaim = Unified.observationRouteForClaim

laneForAntigravityClaim : Anti.AntigravityClaim → CrossPollinationLane
laneForAntigravityClaim Anti.reducedPassiveWeight = observationEvidenceLane
laneForAntigravityClaim Anti.changedFreeFallResponse = observationEvidenceLane
laneForAntigravityClaim Anti.remoteRepulsiveField = observationEvidenceLane
laneForAntigravityClaim Anti.alteredInertialResponse = yangMillsSourceLane
laneForAntigravityClaim Anti.persistentPropulsiveImpulse = navierStokesConfounderLane
laneForAntigravityClaim Anti.engineeredMetricResponse = observationEvidenceLane

inertialClaimDoesNotRouteToGravityEvidence :
  laneForAntigravityClaim Anti.alteredInertialResponse ≡ observationEvidenceLane → ⊥
inertialClaimDoesNotRouteToGravityEvidence ()

impulseClaimDoesNotRouteToGravityEvidence :
  laneForAntigravityClaim Anti.persistentPropulsiveImpulse ≡ observationEvidenceLane → ⊥
impulseClaimDoesNotRouteToGravityEvidence ()

laneForWaveResidual : Wave.WaveTestResidual → CrossPollinationLane
laneForWaveResidual Wave.missingCalibratedData = observationEvidenceLane
laneForWaveResidual Wave.missingGRWaveformComparator = grTheoryLane
laneForWaveResidual Wave.missingAlternativeComparator = grTheoryLane
laneForWaveResidual Wave.missingDetectorResponse = observationEvidenceLane
laneForWaveResidual Wave.missingPropagationModel = grTheoryLane
laneForWaveResidual Wave.missingPopulationModel = grTheoryLane
laneForWaveResidual Wave.missingSystematicErrorBudget = observationEvidenceLane
laneForWaveResidual Wave.residualConsistentWithZero = unificationConsumerLane
laneForWaveResidual Wave.residualRequiresFurtherModelComparison = unificationConsumerLane

laneForMultiScaleResidual : Multi.MultiScaleResidual → CrossPollinationLane
laneForMultiScaleResidual Multi.missingObservationScaleContext = observationEvidenceLane
laneForMultiScaleResidual Multi.missingExactScaleSlotReceipt = observationEvidenceLane
laneForMultiScaleResidual Multi.missingSameTheoryIdentityReceipt = grTheoryLane
laneForMultiScaleResidual Multi.missingSameTheoryFamilyReceipt = grTheoryLane
laneForMultiScaleResidual Multi.missingEvaluationFingerprintWeld = grTheoryLane
laneForMultiScaleResidual Multi.missingLaboratoryFreeFallComparison = observationEvidenceLane
laneForMultiScaleResidual Multi.missingLaboratoryClockComparison = observationEvidenceLane
laneForMultiScaleResidual Multi.missingOrbitalTimingComparison = observationEvidenceLane
laneForMultiScaleResidual Multi.missingCompactBinaryComparison = observationEvidenceLane
laneForMultiScaleResidual Multi.missingNanohertzTimingComparison = observationEvidenceLane
laneForMultiScaleResidual Multi.missingCosmologicalPropagationComparison = observationEvidenceLane
laneForMultiScaleResidual Multi.inconsistentCrossScalePrediction = unificationConsumerLane
laneForMultiScaleResidual Multi.unresolvedCrossScaleSystematics = observationEvidenceLane

producerForMultiScaleResidual : Multi.MultiScaleResidual → Search.ProducerClass
producerForMultiScaleResidual Multi.missingObservationScaleContext = Search.discriminatorProducer
producerForMultiScaleResidual Multi.missingExactScaleSlotReceipt = Search.identityProducer
producerForMultiScaleResidual Multi.missingSameTheoryIdentityReceipt = Search.identityProducer
producerForMultiScaleResidual Multi.missingSameTheoryFamilyReceipt = Search.identityProducer
producerForMultiScaleResidual Multi.missingEvaluationFingerprintWeld = Search.identityProducer
producerForMultiScaleResidual Multi.missingLaboratoryFreeFallComparison = Search.empiricalEvidenceProducer
producerForMultiScaleResidual Multi.missingLaboratoryClockComparison = Search.empiricalEvidenceProducer
producerForMultiScaleResidual Multi.missingOrbitalTimingComparison = Search.empiricalEvidenceProducer
producerForMultiScaleResidual Multi.missingCompactBinaryComparison = Search.empiricalEvidenceProducer
producerForMultiScaleResidual Multi.missingNanohertzTimingComparison = Search.empiricalEvidenceProducer
producerForMultiScaleResidual Multi.missingCosmologicalPropagationComparison = Search.empiricalEvidenceProducer
producerForMultiScaleResidual Multi.inconsistentCrossScalePrediction = Search.contradictionProducer
producerForMultiScaleResidual Multi.unresolvedCrossScaleSystematics = Search.empiricalEvidenceProducer

record GravitationalCrossPollinationBoundary : Set where
  constructor gravitational-cross-pollination-boundary
  field
    observationResidualMayScheduleResearch : Bool
    antigravityRouteIsReusedRatherThanDuplicated : Bool
    inertialAndMomentumClaimsStayOutOfGravityObservation : Bool
    residualShapeTransfersNavierStokesClayProof : Bool
    residualShapeTransfersYangMillsMassGapProof : Bool
    spectralAnalogyTransfersRiemannHypothesisProof : Bool
    waveResidualAutomaticallyPromotesModifiedGravity : Bool
    antigravityResidualAutomaticallyPromotesUnification : Bool
    oneScaleGravityFitAutomaticallyClosesMultiScaleFingerprint : Bool
    ordinaryFluidClosureMayRefineLocalForceInterpretation : Bool
    gaugeSourceAnalysisMayRefineHighFieldInterpretation : Bool
    jointCrossScaleResidualMayReachUnificationConsumer : Bool

canonicalGravitationalCrossPollinationBoundary : GravitationalCrossPollinationBoundary
canonicalGravitationalCrossPollinationBoundary =
  gravitational-cross-pollination-boundary
    true true true false false false false false false true true true

existingCoreTheoremInterfaces : Core.CoreTheoremInterfaces
existingCoreTheoremInterfaces = Core.canonicalCoreTheoremInterfaces
existingMultiScaleBoundary : Multi.MultiScaleTheoryBoundary
existingMultiScaleBoundary = Multi.canonicalMultiScaleTheoryBoundary

navierStokesTerminalStillFalse : Core.coreNavierStokesTerminalFalse ≡ Core.coreNavierStokesTerminalFalse
navierStokesTerminalStillFalse = refl
yangMillsTerminalStillFalse : Core.coreYangMillsTerminalFalse ≡ Core.coreYangMillsTerminalFalse
yangMillsTerminalStillFalse = refl
unificationTerminalStillFalse : Core.coreUnificationTerminalFalse ≡ Core.coreUnificationTerminalFalse
unificationTerminalStillFalse = refl
