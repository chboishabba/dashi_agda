module DASHI.Interop.GravitationalObservationUnificationBidiCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.GR.GravitationalObservationBidiExact as Obs
import DASHI.Physics.GR.GravitationalWaveTheoryTestBidiExact as Wave
import DASHI.Physics.GR.GravitationalPredictionObservationBidiExact as Pred
import DASHI.Physics.GR.GravitationalMultiScaleTheoryFingerprintBidiExact as Multi
import DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact as Anti
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search
import DASHI.Papers.CoreTheoremInterfaces as Core

------------------------------------------------------------------------
-- GRAVITATIONAL OBSERVATION / ANTIGRAVITY / UNIFICATION CROSS-POLLINATION
------------------------------------------------------------------------

data CrossPollinationLane : Set where
  observationEvidenceLane : CrossPollinationLane
  grTheoryLane : CrossPollinationLane
  navierStokesConfounderLane : CrossPollinationLane
  yangMillsSourceLane : CrossPollinationLane
  riemannMethodLane : CrossPollinationLane
  unificationConsumerLane : CrossPollinationLane

data CrossPollinationRole : Set where
  acquireEvidence : CrossPollinationRole
  compareGravityTheory : CrossPollinationRole
  closeOrdinaryMomentum : CrossPollinationRole
  constrainGaugeSource : CrossPollinationRole
  borrowProofDisciplineOnly : CrossPollinationRole
  registerCrossSectorResidual : CrossPollinationRole

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

observationChannelForAntigravityClaim : Anti.AntigravityClaim → Obs.GravitationalObservationChannel
observationChannelForAntigravityClaim Anti.reducedPassiveWeight = Obs.freeFallEquivalence
observationChannelForAntigravityClaim Anti.changedFreeFallResponse = Obs.freeFallEquivalence
observationChannelForAntigravityClaim Anti.remoteRepulsiveField = Obs.localTestMassAcceleration
observationChannelForAntigravityClaim Anti.alteredInertialResponse = Obs.freeFallEquivalence
observationChannelForAntigravityClaim Anti.persistentPropulsiveImpulse = Obs.localTestMassAcceleration
observationChannelForAntigravityClaim Anti.engineeredMetricResponse = Obs.clockOrRedshift

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
    true false false false false false false true true true

existingCoreTheoremInterfaces : Core.CoreTheoremInterfaces
existingCoreTheoremInterfaces = Core.canonicalCoreTheoremInterfaces

existingMultiScaleBoundary : Multi.MultiScaleTheoryBoundary
existingMultiScaleBoundary = Multi.canonicalMultiScaleTheoryBoundary

navierStokesTerminalStillFalse :
  Core.coreNavierStokesTerminalFalse ≡ Core.coreNavierStokesTerminalFalse
navierStokesTerminalStillFalse = refl

yangMillsTerminalStillFalse :
  Core.coreYangMillsTerminalFalse ≡ Core.coreYangMillsTerminalFalse
yangMillsTerminalStillFalse = refl

unificationTerminalStillFalse :
  Core.coreUnificationTerminalFalse ≡ Core.coreUnificationTerminalFalse
unificationTerminalStillFalse = refl
