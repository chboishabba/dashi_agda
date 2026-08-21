module DASHI.Cognition.PNF.ControlledDecisionHyperformalismExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import DASHI.Biology.AllostaticBodyStateExact as Allostatic
import DASHI.Biology.InteroceptiveRefreshCalibrationExact as Refresh
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
import DASHI.Cognition.PNF.QuantumDecisionInstrumentHierarchyExact as Instrument

------------------------------------------------------------------------
-- CONTROLLED DECISION HYPERFORMALISM
--
-- A strict extension of DecisionFibrePotentialHyperformalismExact.  The base
-- object remains authoritative for access/candidate/audit/potential/commitment/
-- actuation/learning.  This layer adds only the coordinates demonstrated to be
-- independently stateful by the converging literature:
--
-- evidence, dynamic threshold, confidence, conflict, allostatic body,
-- interoception/felt state, nonequilibrium flux, and exact finite variational
-- structure.
------------------------------------------------------------------------

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
  Confidence.sameConfidenceDifferentEvidenceHistory .Data.Product.proj₁
  where
    open import Data.Product using (proj₁)

sameEvidenceCanCommitAtDifferentThresholds :
  Threshold.thresholdUnder Threshold.lowerThreshold Threshold.Evidence.e1
  ≡ Threshold.thresholdUnder Threshold.elevatedThreshold Threshold.Evidence.e1 → ⊥
sameEvidenceCanCommitAtDifferentThresholds =
  Threshold.sameEvidenceDifferentThresholdChangesCommitment

formalAuditCannotDetermineResponseConflict :
  _ → ⊥
formalAuditCannotDetermineResponseConflict = Conflict.formalAuditCannotDetermineConflict

scalarPotentialCannotDetermineFluxOutcome :
  _ → ⊥
scalarPotentialCannotDetermineFluxOutcome = Landscape.potentialCannotDetermineFlowOutcome

potentialCannotRecoverNoncommutingHistory :
  _ → ⊥
potentialCannotRecoverNoncommutingHistory = LandscapeOrder.potentialCannotRecoverOrderedHistory

extinctionStillNotErasure :
  LearningMechanism.extinctionUpdate ≡ LearningMechanism.erasureUpdate → ⊥
extinctionStillNotErasure = LearningMechanism.extinctionIsNotErasure

extinctionStillNotReconsolidation :
  LearningMechanism.extinctionUpdate ≡ LearningMechanism.reconsolidationUpdate → ⊥
extinctionStillNotReconsolidation = LearningMechanism.extinctionIsNotReconsolidation

generalizedInstrumentDoesNotForceQQ :
  Instrument.Order.QQSatisfied
    (Instrument.GeneralizedInstrumentWitness.counts
      Instrument.canonicalGeneralizedInstrumentWitness) → ⊥
generalizedInstrumentDoesNotForceQQ = Instrument.generalizedInstrumentDoesNotForceQQ

mobilisedBodyDoesNotDetermineAutonomy :
  _ → ⊥
mobilisedBodyDoesNotDetermineAutonomy = Controlled.bodyStateCannotDetermineAutonomyAxes
