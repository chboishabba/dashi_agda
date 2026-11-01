module DASHI.Cognition.FibreBraidActionTraceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import Base369 as Base
import DASHI.Cognition.FibreBraidReasoning as Reasoning
import DASHI.Core.ActionCrossingTraceCalculusExact as Trace

------------------------------------------------------------------------
-- EXPLICIT ACTION TRACE FOR THE EXISTING FIBRE-BRAID REASONING DYNAMICS
--
-- FibreBraidReasoning already owns the dynamics:
--   transportBraid : List TriTruth -> TriTruth -> TriTruth
--
-- This owner adds only the missing provenance grammar.  Each auxiliary trit is
-- recorded as one ordered crossing of an auxiliary reasoning strand with the
-- latent strand.  Evaluating the resulting ActionTrace is definitionally the
-- existing transportBraid; no new reasoning dynamics are introduced.
------------------------------------------------------------------------

data ReasoningStrand : Set where
  latentReasoningStrand : ReasoningStrand
  auxiliaryReasoningStrand : ReasoningStrand

auxiliaryCrossing :
  Base.TriTruth → Trace.CrossingEvent ReasoningStrand Base.TriTruth
auxiliaryCrossing auxiliary =
  Trace.crossing-event
    auxiliaryReasoningStrand
    latentReasoningStrand
    auxiliary

reasoningBraidTrace :
  List Base.TriTruth → Trace.ActionTrace ReasoningStrand Base.TriTruth
reasoningBraidTrace [] = []
reasoningBraidTrace (auxiliary ∷ rest) =
  auxiliaryCrossing auxiliary ∷ reasoningBraidTrace rest

evaluateReasoningTrace :
  Trace.ActionTrace ReasoningStrand Base.TriTruth →
  Base.TriTruth → Base.TriTruth
evaluateReasoningTrace [] value = value
evaluateReasoningTrace (event ∷ rest) value =
  evaluateReasoningTrace rest
    (Base.triXor (Trace.action event) value)

traceRealizesTransportBraid :
  (auxiliaries : List Base.TriTruth) →
  (value : Base.TriTruth) →
  evaluateReasoningTrace (reasoningBraidTrace auxiliaries) value
  ≡ Reasoning.transportBraid auxiliaries value
traceRealizesTransportBraid [] value = refl
traceRealizesTransportBraid (auxiliary ∷ rest) value =
  traceRealizesTransportBraid rest (Base.triXor auxiliary value)

canonicalTrace : Trace.ActionTrace ReasoningStrand Base.TriTruth
canonicalTrace = reasoningBraidTrace (Base.tri-high ∷ [])

canonicalTraceReachesExistingResolvedLatentValue :
  evaluateReasoningTrace canonicalTrace
    (Reasoning.latentValue Reasoning.initialReasoningState)
  ≡ Reasoning.latentValue Reasoning.resolvedByHighAuxiliary
canonicalTraceReachesExistingResolvedLatentValue = refl

canonicalTraceLowersDefect :
  Reasoning.globalReasoningDefect Reasoning.resolvedByHighAuxiliary ≡ 1
canonicalTraceLowersDefect = Reasoning.auxiliaryTransportLowersDefect

------------------------------------------------------------------------
-- Ordered history remains explicit even when endpoint action forgets order.
------------------------------------------------------------------------

traceConcatenationKeepsExistingEvaluationOrder :
  (left right : List Base.TriTruth) →
  (value : Base.TriTruth) →
  evaluateReasoningTrace
    (reasoningBraidTrace left Trace.++trace reasoningBraidTrace right)
    value
  ≡
  Reasoning.transportBraid right (Reasoning.transportBraid left value)
traceConcatenationKeepsExistingEvaluationOrder [] right value =
  traceRealizesTransportBraid right value
traceConcatenationKeepsExistingEvaluationOrder (auxiliary ∷ rest) right value =
  traceConcatenationKeepsExistingEvaluationOrder
    rest right (Base.triXor auxiliary value)

highThenMidTrace : Trace.ActionTrace ReasoningStrand Base.TriTruth
highThenMidTrace =
  reasoningBraidTrace (Base.tri-high ∷ Base.tri-mid ∷ [])

midThenHighTrace : Trace.ActionTrace ReasoningStrand Base.TriTruth
midThenHighTrace =
  reasoningBraidTrace (Base.tri-mid ∷ Base.tri-high ∷ [])

sameEndpointDifferentOrderedTrace :
  evaluateReasoningTrace highThenMidTrace Base.tri-low
  ≡ evaluateReasoningTrace midThenHighTrace Base.tri-low
sameEndpointDifferentOrderedTrace = refl

orderedTracesAreDistinct : highThenMidTrace ≡ midThenHighTrace → ⊥
orderedTracesAreDistinct ()

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data ReasoningActionTraceIsBraidGroupElement : Set where

data SameFinalLatentValueDeterminesCrossingHistory : Set where

data TriXorAssociativityErasesActionOrder : Set where

traceDoesNotPromoteBraidGroup :
  ReasoningActionTraceIsBraidGroupElement → ⊥
traceDoesNotPromoteBraidGroup ()

sameFinalValueDoesNotDetermineCrossingHistory :
  SameFinalLatentValueDeterminesCrossingHistory → ⊥
sameFinalValueDoesNotDetermineCrossingHistory ()

associativityDoesNotEraseActionOrder :
  TriXorAssociativityErasesActionOrder → ⊥
associativityDoesNotEraseActionOrder ()

record FibreBraidActionTraceBoundary : Set where
  constructor fibre-braid-action-trace-boundary
  field
    existingTransportBraidDynamicsReused : Bool
    auxiliaryActionsBecomeExplicitCrossings : Bool
    traceEvaluationEqualsExistingTransport : Bool
    crossingOrderRetainedAsHistory : Bool
    endpointMayForgetCrossingOrder : Bool
    actionTracePromotedToBraidGroup : Bool
    actionTracePromotedToBraidGroupIsFalse :
      actionTracePromotedToBraidGroup ≡ false
    finalLatentValueDeterminesTrace : Bool
    finalLatentValueDeterminesTraceIsFalse :
      finalLatentValueDeterminesTrace ≡ false
    associativityErasesActionOrder : Bool
    associativityErasesActionOrderIsFalse :
      associativityErasesActionOrder ≡ false
    boundaryNote : String

open FibreBraidActionTraceBoundary public

canonicalFibreBraidActionTraceBoundary : FibreBraidActionTraceBoundary
canonicalFibreBraidActionTraceBoundary =
  fibre-braid-action-trace-boundary
    true
    true
    true
    true
    true
    false refl
    false refl
    false refl
    "The existing FibreBraidReasoning transport is represented as an ordered ActionTrace with explicit auxiliary/latent crossings. Trace evaluation is extensionally the old transportBraid. In the triXor carrier, high-then-mid and mid-then-high reach the same endpoint while remaining distinct ordered traces, so provenance cannot be reconstructed from endpoint state. No braid-group claim is promoted."
