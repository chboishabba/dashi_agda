module DASHI.Cognition.PNF.ControlledDecisionHyperformalismExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Product using (proj₁)

import DASHI.Biology.AllostaticBodyStateExact as Allostatic
import DASHI.Biology.InteroceptiveRefreshCalibrationExact as Refresh
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Cognition.PNF.BoundedEvidenceCommitmentExact as Evidence
import DASHI.Cognition.PNF.ControlledDecisionDynamicalSystemExact as System
import DASHI.Cognition.PNF.ControlledDecisionStateExact as Controlled
import DASHI.Cognition.PNF.DecisionConfidenceNoncollapseExact as Confidence
import DASHI.Cognition.PNF.DecisionConflictAuditSeparationExact as Conflict
import DASHI.Cognition.PNF.DecisionFibrePotentialHyperformalismExact as Base
import DASHI.Cognition.PNF.DecisionLandscapeFluxExact as Landscape
import DASHI.Cognition.PNF.EmbodiedDecisionControlBridgeExact as EmbodiedControl
import DASHI.Cognition.PNF.FiniteVariationalFreeEnergyExact as Variational
import DASHI.Cognition.PNF.LandscapeFluxOrderBridgeExact as LandscapeOrder
import DASHI.Cognition.PNF.LearningUpdateMechanismSeparationExact as LearningMechanism
import DASHI.Cognition.PNF.NeuromodulatedCommitmentThresholdExact as Threshold
import DASHI.Cognition.PNF.NoncommutativeDecisionUpdateQQExact as Order
import DASHI.Cognition.PNF.QuantumDecisionInstrumentHierarchyExact as Instrument

record ControlledDecisionHyperformalism : Set₁ where
  constructor controlledDecisionHyperformalism
  field
    baseDecisionFormalism : Base.DecisionFibrePotentialHyperformalism
    controlledStateBoundary : Controlled.ControlledDecisionStateBoundary
    controlledSystemBoundary : System.ControlledDecisionSystemBoundary
    confidenceBoundary : Confidence.ConfidenceBoundary
    thresholdBoundary : Threshold.NeuromodulatedThresholdBoundary
    conflictBoundary : Conflict.DecisionConflictAuditBoundary
    landscapeFluxBoundary : Landscape.DecisionLandscapeFluxBoundary
    allostaticBoundary : Allostatic.AllostaticBodyStateBoundary
    interoceptiveControlBoundary : EmbodiedControl.EmbodiedDecisionControlBoundary
    refreshBoundary : Refresh.InteroceptiveRefreshBoundary
    variationalBoundary : Variational.FiniteVariationalFreeEnergyBoundary
    learningMechanismBoundary : LearningMechanism.LearningUpdateMechanismBoundary
    instrumentHierarchyBoundary : Instrument.QuantumDecisionInstrumentHierarchyBoundary

open ControlledDecisionHyperformalism public

canonicalControlledDecisionHyperformalism : ControlledDecisionHyperformalism
canonicalControlledDecisionHyperformalism =
  controlledDecisionHyperformalism
    Base.canonicalDecisionFibrePotentialHyperformalism
    Controlled.canonicalControlledDecisionStateBoundary
    System.canonicalControlledDecisionSystemBoundary
    Confidence.canonicalConfidenceBoundary
    Threshold.canonicalNeuromodulatedThresholdBoundary
    Conflict.canonicalDecisionConflictAuditBoundary
    Landscape.canonicalDecisionLandscapeFluxBoundary
    Allostatic.canonicalAllostaticBodyStateBoundary
    EmbodiedControl.canonicalEmbodiedDecisionControlBoundary
    Refresh.canonicalInteroceptiveRefreshBoundary
    Variational.canonicalFiniteVariationalFreeEnergyBoundary
    LearningMechanism.canonicalLearningUpdateMechanismBoundary
    Instrument.canonicalQuantumDecisionInstrumentHierarchyBoundary

sameCommitmentNeedNotMeanSameConfidence :
  Confidence.commitment Confidence.committedLowConfidence
  ≡ Confidence.commitment Confidence.committedHighConfidence
sameCommitmentNeedNotMeanSameConfidence = Confidence.sameCommitmentDifferentConfidence

sameConfidenceNeedNotMeanSameEvidenceHistory :
  Confidence.historyConfidence Confidence.highConfidenceAfterOne
  ≡ Confidence.historyConfidence Confidence.highConfidenceAfterTwo
sameConfidenceNeedNotMeanSameEvidenceHistory =
  proj₁ Confidence.sameConfidenceDifferentEvidenceHistory

sameEvidenceCanCommitAtDifferentThresholds :
  Threshold.thresholdUnder Threshold.lowerThreshold Evidence.e1
  ≡ Threshold.thresholdUnder Threshold.elevatedThreshold Evidence.e1 → ⊥
sameEvidenceCanCommitAtDifferentThresholds =
  Threshold.sameEvidenceDifferentThresholdChangesCommitment

formalAuditCannotDetermineResponseConflict :
  NF.FactorsThrough Conflict.formalAudit Conflict.responseConflict → ⊥
formalAuditCannotDetermineResponseConflict = Conflict.formalAuditCannotDetermineConflict

scalarPotentialCannotDetermineFluxOutcome :
  NF.FactorsThrough Landscape.potential Landscape.flowOutcome → ⊥
scalarPotentialCannotDetermineFluxOutcome = Landscape.potentialCannotDetermineFlowOutcome

potentialCannotRecoverNoncommutingHistory :
  NF.FactorsThrough LandscapeOrder.potentialObservation LandscapeOrder.beliefState → ⊥
potentialCannotRecoverNoncommutingHistory = LandscapeOrder.potentialCannotRecoverOrderedHistory

extinctionStillNotErasure :
  LearningMechanism.extinctionUpdate ≡ LearningMechanism.erasureUpdate → ⊥
extinctionStillNotErasure = LearningMechanism.extinctionIsNotErasure

extinctionStillNotReconsolidation :
  LearningMechanism.extinctionUpdate ≡ LearningMechanism.reconsolidationUpdate → ⊥
extinctionStillNotReconsolidation = LearningMechanism.extinctionIsNotReconsolidation

generalizedInstrumentDoesNotForceQQ :
  Order.QQSatisfied
    (Instrument.GeneralizedInstrumentWitness.counts
      Instrument.canonicalGeneralizedInstrumentWitness) → ⊥
generalizedInstrumentDoesNotForceQQ = Instrument.generalizedInstrumentDoesNotForceQQ

mobilisedBodyDoesNotDetermineAutonomy :
  NF.FactorsThrough Controlled.bodyProjection Controlled.autonomyProjection → ⊥
mobilisedBodyDoesNotDetermineAutonomy = Controlled.bodyStateCannotDetermineAutonomyAxes
