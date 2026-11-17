module DASHI.Quantum.ZorroTSFVPostselectionNoSignalExact where

open import DASHI.Core.Prelude

import DASHI.Quantum.TSVF as OriginalTSFV
import DASHI.Foundations.TwoBoundarySystem as TwoBoundary
import DASHI.Physics.Closure.TSFVBidirectionalCausticBridgeExact as HistoryAction

------------------------------------------------------------------------
-- BOUNDED COUNTEREXAMPLE TO:
--  "future-conditioned records differ" => "past was altered".
--
-- OriginalTSFV owns the quantum interface/ABL conditional surface.
-- TwoBoundary owns the generic bi-directional boundary architecture.
-- HistoryAction owns history -> action/phase -> observation order.
-- None of them supplies a freely controlled earlier-event intervention.
--
-- This 2x2 construction is CLASSICAL, not a concrete Hilbert-space
-- realisation or a theorem about every physically conceivable process.
------------------------------------------------------------------------

data EarlierBit : Set where
  earlierZero : EarlierBit
  earlierOne : EarlierBit

data LaterSelection : Set where
  selectZero : LaterSelection
  selectOne : LaterSelection

-- A complete preselected population: one of each earlier outcome for
-- either later choice. This is a finite count, not a probability.
preselectedCount : LaterSelection → EarlierBit → Nat
preselectedCount _ _ = 1

preselectedInvariant :
  (a b : LaterSelection) (x : EarlierBit) →
  preselectedCount a x ≡ preselectedCount b x
preselectedInvariant _ _ _ = refl

-- Two different later filters *select* different historical subgroups.
-- They do not change the unconditional earlier counts.
postselectedCount : LaterSelection → EarlierBit → Nat
postselectedCount selectZero earlierZero = 1
postselectedCount selectZero earlierOne = 0
postselectedCount selectOne earlierZero = 0
postselectedCount selectOne earlierOne = 1

selectedZeroFavoursEarlierZero :
  postselectedCount selectZero earlierZero ≡ 1
selectedZeroFavoursEarlierZero = refl

selectedZeroExcludesEarlierOne :
  postselectedCount selectZero earlierOne ≡ 0
selectedZeroExcludesEarlierOne = refl

selectedOneExcludesEarlierZero :
  postselectedCount selectOne earlierZero ≡ 0
selectedOneExcludesEarlierZero = refl

selectedOneFavoursEarlierOne :
  postselectedCount selectOne earlierOne ≡ 1
selectedOneFavoursEarlierOne = refl

-- Strictly narrower observational selection is consistent with the
-- same unchanged earlier population; this is a constructive witness.
postselectionWithoutRetrosignal :
  preselectedCount selectZero earlierZero ≡
    preselectedCount selectOne earlierZero
  ×
  postselectedCount selectZero earlierZero ≡ 1
  ×
  postselectedCount selectOne earlierZero ≡ 0
postselectionWithoutRetrosignal = refl , refl , refl

------------------------------------------------------------------------
-- Claim kinds remain non-interchangeable. The required operational
-- controlled-do() effect does not follow from postselection.
------------------------------------------------------------------------

data TemporalClaim : Set where
  backwardConditioning : TemporalClaim
  timeReversalCovariance : TemporalClaim
  anomalousPrediction : TemporalClaim
  freelyControlledEarlierIntervention : TemporalClaim

conditioningNotIntervention :
  backwardConditioning ≡ freelyControlledEarlierIntervention → ⊥
conditioningNotIntervention ()

symmetryNotIntervention :
  timeReversalCovariance ≡ freelyControlledEarlierIntervention → ⊥
symmetryNotIntervention ()

predictionNotIntervention :
  anomalousPrediction ≡ freelyControlledEarlierIntervention → ⊥
predictionNotIntervention ()

record ControlledEarlierEffectEvidence : Set₁ where
  field
    Intervention : Set
    EarlierObservation : Set
    commonEarlierPreparation : Set
    laterIndependentChoice : Set
    exclusionOfOrdinaryLeakage : Set
    sameRecordedEarlierOutcome : Set
    interventionalDistributionDifference : Set
    independentlyReplicated : Set

-- This record is a SCHEMA, not a scientific receipt: an arbitrary caller
-- could choose trivial predicates (such as top) for all of its fields.
-- It is deliberately not used as an authority to promote signalling.
-- A same-object calibration/experimental authority must be supplied by a
-- separately reviewed external-data consumer before any physical claim.
