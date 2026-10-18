{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyFiveSourcePhysicsReceiptResolutionExact where

------------------------------------------------------------------------
-- FIVE SOURCE-PHYSICS RECEIPTS: FAIL-CLOSED RESOLUTION.
--
-- The generic proposition sockets have been removed from this owner.  The exact
-- mathematical interfaces now live in
-- `CMP119CosmologyFiveSourcePhysicsTypedReceiptsExact`.
--
-- A1  selected R144 signed-B4 readout covariance
-- A2  selected R109 insertion -> real cylinder semantics
-- B1  absolute same-sequence R136/R109 direct-tail attachment
-- B2  source-native Eq.(2.23) metric-family strict negative envelope
-- C   embed(Q_R136) <= selected renormalized anomaly trace
--
-- This module records why the current safe theory does not manufacture any of
-- those five evidence values.  No postulate promotion is permitted.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119CosmologyFiveSourcePhysicsTypedReceiptsExact as Typed
import DASHI.Physics.Foundations.CMP119CosmologyE1LinearityDoesNotForceB4CovarianceExact as A1NoGo
import DASHI.Physics.Foundations.CMP119CosmologyR109PairObservableUnderdeterminationExact as A2NoGo
import DASHI.Physics.Foundations.CMP119CosmologyR109AbsoluteExpectationAnchorNoGoExact as B1NoGo
import DASHI.Physics.Foundations.CMP119CosmologyEq223ERBMetricVariationUnderdeterminationExact as B2ERBNoGo
import DASHI.Physics.Foundations.CMP119CosmologyEq223VacuumMetricSignUnderdeterminationExact as B2VacuumNoGo
import DASHI.Physics.Foundations.CMP119CosmologyR136TraceAnomalyOrderDominanceExact as CDominance

------------------------------------------------------------------------
-- Terminal receipt labels.
------------------------------------------------------------------------

data SourcePhysicsReceipt : Set where
  a1-r144-signed-b4-readout-covariance : SourcePhysicsReceipt
  a2-r109-selected-insertion-semantics : SourcePhysicsReceipt
  b1-r136-r109-absolute-direct-tail-attachment : SourcePhysicsReceipt
  b2-eq223-source-metric-family-negative-envelope : SourcePhysicsReceipt
  c-r136-below-selected-anomaly-trace : SourcePhysicsReceipt

terminalSourcePhysicsReceiptCount : Nat
terminalSourcePhysicsReceiptCount = Typed.typedSourcePhysicsReceiptCount

genericSetValuedSocketsEliminated : Bool
genericSetValuedSocketsEliminated = true

------------------------------------------------------------------------
-- Audit facts: why no compiler can manufacture the five receipts.
------------------------------------------------------------------------

a1RequiresSourceDifferentiatedChangeOfVariables : Bool
a1RequiresSourceDifferentiatedChangeOfVariables = true

a1AdditiveFirstVariationLinearityIsInsufficient : Bool
a1AdditiveFirstVariationLinearityIsInsufficient =
  A1NoGo.r142LinearityIsNotAnE1CovarianceProducerByItself

a2RequiresSelectedInsertionSemantics : Bool
a2RequiresSelectedInsertionSemantics = true

a2BarePairUnderdetermined : Bool
a2BarePairUnderdetermined =
  A2NoGo.remainingE2E4LeafIsSourceSemanticsEvaluator

b1RequiresAbsoluteSameSequenceTailAttachment : Bool
b1RequiresAbsoluteSameSequenceTailAttachment = true

b1DifferenceDataUnderdetermined : Bool
b1DifferenceDataUnderdetermined =
  B1NoGo.absoluteExpectationAnchorIsGenuineAdditionalInformation

b2RequiresSourceMetricFamilyCalibration : Bool
b2RequiresSourceMetricFamilyCalibration = true

b2RawEq223MetricSignUnderdetermined : Bool
b2RawEq223MetricSignUnderdetermined =
  B2ERBNoGo.sourceBackedERBMetricVariationStillRequired

b2RawEq223VacuumSignUnderdetermined : Bool
b2RawEq223VacuumSignUnderdetermined =
  B2VacuumNoGo.sourceBackedVacuumMetricVariationStillRequired

cRequiresR136BelowSelectedAnomalyTrace : Bool
cRequiresR136BelowSelectedAnomalyTrace =
  CDominance.remainingFallbackPhysicalLeafIsR136BelowSelectedAnomalyTrace

cExactReadoutEqualityIsParetoOverstrong : Bool
cExactReadoutEqualityIsParetoOverstrong =
  CDominance.anomalyFallbackExactEqualityIsParetoOverstrong

cTraceAnomalyCitationAloneInsufficient : Bool
cTraceAnomalyCitationAloneInsufficient = true

------------------------------------------------------------------------
-- Promotion firewall.
------------------------------------------------------------------------

allFivePaidByCurrentSafeTheory : Bool
allFivePaidByCurrentSafeTheory = Typed.currentSafeTheoryPaysAllFiveTypedReceipts

addingPostulatesWouldNotCountAsSourcePhysicsCompletion : Bool
addingPostulatesWouldNotCountAsSourcePhysicsCompletion = true

remainingWorkIsExternalEvidenceOrNewSourceCalculation : Bool
remainingWorkIsExternalEvidenceOrNewSourceCalculation = true
