module DASHI.Cognition.PNF.ControlledDecisionDynamicsRegression where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (_+_)

import DASHI.Biology.AllostaticBodyStateExact as Allostatic
import DASHI.Biology.EmbodiedOptionConeInteroceptionExact as Embodied
import DASHI.Biology.InteroceptiveRefreshCalibrationExact as Refresh
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Cognition.PNF.BoundedEvidenceCommitmentExact as Evidence
import DASHI.Cognition.PNF.ControlledDecisionDynamicalSystemExact as System
import DASHI.Cognition.PNF.ControlledDecisionHyperformalismExact as ControlledRoot
import DASHI.Cognition.PNF.ControlledDecisionStateExact as Controlled
import DASHI.Cognition.PNF.DecisionConfidenceNoncollapseExact as Confidence
import DASHI.Cognition.PNF.DecisionConflictAuditSeparationExact as Conflict
import DASHI.Cognition.PNF.DecisionLandscapeFluxExact as Landscape
import DASHI.Cognition.PNF.EmbodiedDecisionControlBridgeExact as EmbodiedControl
import DASHI.Cognition.PNF.FiniteVariationalFreeEnergyExact as Variational
import DASHI.Cognition.PNF.LandscapeFluxOrderBridgeExact as LandscapeOrder
import DASHI.Cognition.PNF.LearningUpdateMechanismSeparationExact as Learning
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PNF.NeuromodulatedCommitmentThresholdExact as Threshold
import DASHI.Cognition.PNF.NoncommutativeDecisionUpdateQQExact as Order
import DASHI.Cognition.PNF.QuantumDecisionInstrumentHierarchyExact as Instrument

regressionControlledRootExists : ControlledRoot.ControlledDecisionHyperformalism
regressionControlledRootExists = ControlledRoot.canonicalControlledDecisionHyperformalism

regressionSameCommitmentDifferentConfidence :
  Confidence.commitment Confidence.committedLowConfidence
  ≡ Confidence.commitment Confidence.committedHighConfidence
regressionSameCommitmentDifferentConfidence = Confidence.sameCommitmentDifferentConfidence

regressionConfidenceDoesNotRecoverEvidenceHistory :
  NF.FactorsThrough Confidence.historyConfidence Confidence.evidenceHistory → ⊥
regressionConfidenceDoesNotRecoverEvidenceHistory =
  Confidence.confidenceCannotRecoverEvidenceHistory

regressionSameEvidenceDifferentThreshold :
  Threshold.thresholdUnder Threshold.lowerThreshold Evidence.e1
  ≡ Threshold.thresholdUnder Threshold.elevatedThreshold Evidence.e1 → ⊥
regressionSameEvidenceDifferentThreshold =
  Threshold.sameEvidenceDifferentThresholdChangesCommitment

regressionThresholdCanShiftCommitmentTime :
  Threshold.commitmentTime Threshold.lowerThreshold
  ≡ Threshold.commitmentTime Threshold.elevatedThreshold → ⊥
regressionThresholdCanShiftCommitmentTime = Threshold.thresholdPolicyCanShiftCommitmentTime

regressionConflictIsNotFormalAudit :
  NF.FactorsThrough Conflict.formalAudit Conflict.responseConflict → ⊥
regressionConflictIsNotFormalAudit = Conflict.formalAuditCannotDetermineConflict

regressionPotentialDoesNotDetermineFlow :
  NF.FactorsThrough Landscape.potential Landscape.flowOutcome → ⊥
regressionPotentialDoesNotDetermineFlow = Landscape.potentialCannotDetermineFlowOutcome

regressionPotentialDoesNotRecoverOrderedHistory :
  NF.FactorsThrough LandscapeOrder.potentialObservation LandscapeOrder.beliefState → ⊥
regressionPotentialDoesNotRecoverOrderedHistory = LandscapeOrder.potentialCannotRecoverOrderedHistory

regressionExtinctionNotErasure :
  Learning.extinctionUpdate ≡ Learning.erasureUpdate → ⊥
regressionExtinctionNotErasure = Learning.extinctionIsNotErasure

regressionExtinctionNotReconsolidation :
  Learning.extinctionUpdate ≡ Learning.reconsolidationUpdate → ⊥
regressionExtinctionNotReconsolidation = Learning.extinctionIsNotReconsolidation

regressionGeneralInstrumentDoesNotForceQQ :
  Order.QQSatisfied
    (Instrument.GeneralizedInstrumentWitness.counts
      Instrument.canonicalGeneralizedInstrumentWitness) → ⊥
regressionGeneralInstrumentDoesNotForceQQ = Instrument.generalizedInstrumentDoesNotForceQQ

regressionFiniteVariationalIdentity :
  (law : Variational.TwoStateVariationalLaw) →
  Variational.klDivergence law
  ≡ Variational.variationalFreeEnergy law + Variational.logPartition law
regressionFiniteVariationalIdentity = Variational.klEqualsFreeEnergyPlusLogPartition

regressionAllostaticCoreDoesNotExhaustState :
  NF.FactorsThrough Allostatic.coreProjection Allostatic.immuneProjection → ⊥
regressionAllostaticCoreDoesNotExhaustState =
  Allostatic.coreBodyDoesNotDetermineFullAllostaticState

regressionSameBodyPriorCanChangeDecisionControl :
  EmbodiedControl.accessMode
    (EmbodiedControl.bodyToDecisionControl Embodied.safetyPrior Embodied.mobilisedBody)
  ≡ EmbodiedControl.accessMode
    (EmbodiedControl.bodyToDecisionControl Embodied.threatPrior Embodied.mobilisedBody) → ⊥
regressionSameBodyPriorCanChangeDecisionControl =
  EmbodiedControl.sameMobilisedBodyDifferentPriorChangesControl

regressionBodyStateCannotDetermineAutonomy :
  NF.FactorsThrough Controlled.bodyProjection Controlled.autonomyProjection → ⊥
regressionBodyStateCannotDetermineAutonomy = Controlled.bodyStateCannotDetermineAutonomyAxes

regressionControlledTransitionMovesHiddenLandscape :
  (memory : Memory.MemoryFibre) →
  System.landscapePosition
    (System.transition (System.canonicalSystemState memory)
      System.applyClockwiseFlux System.noExternalObservation)
  ≡ Landscape.saddle
regressionControlledTransitionMovesHiddenLandscape = System.clockwiseInputMovesCanonicalLandscape

regressionCraigRefreshCalibration : Refresh.candidateRefreshMilliseconds ≡ 125
regressionCraigRefreshCalibration = Refresh.candidateCalibrationPinned
