module DASHI.Physics.QuantumSensors.NVTSFVHistoryOpticalNonidentifiabilityExact where

-- Uses existing TSFV bidirectional-history / caustic observation and
-- history-conditioned choice owners. A time-coarse optical scalar can
-- fail to identify the underlying ordered history even with exact
-- detector arithmetic. This is a formal negative control, not an
-- empirical claim about a specific diamond NV experiment.

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Data.Rational.Base using (ℚ)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.TSFVBidirectionalCausticBridgeExact as Caustic
import DASHI.Physics.Closure.TSFVHistoryConditionedChoiceBridgeExact as Choice
import DASHI.Physics.Foundations.FiniteHistoryFunctionalExact as History

-- Calibration parameters may assign a photon mean to each projected
-- observation category, but not recover information already discarded.
record CoarseOpticalMap : Set where
  constructor coarse-optical-map
  field
    focusedPhotonMean diffusePhotonMean : ℚ
open CoarseOpticalMap public

photonMeanForObservation :
  CoarseOpticalMap → Caustic.HistoryObservation → ℚ
photonMeanForObservation detector Caustic.focusedHistoryObservation =
  focusedPhotonMean detector
photonMeanForObservation detector Caustic.diffuseHistoryObservation =
  diffusePhotonMean detector

coarsePhotonMean : CoarseOpticalMap → History.History3 → ℚ
coarsePhotonMean detector h =
  photonMeanForObservation detector (Caustic.historyProjection h)

twoHistoriesOneOpticalMean :
  (detector : CoarseOpticalMap) →
  coarsePhotonMean detector History.historyABC
    ≡ coarsePhotonMean detector History.historyACB
twoHistoriesOneOpticalMean detector = refl

-- This no-go is about arbitrary *history-sensitive* choices:
-- a scalar decoder cannot recover two different choices from the
-- exactly same coarse photon mean for both histories.
cannotRecoverHistoryChoiceFromOpticalMean :
  (detector : CoarseOpticalMap) →
  (decode : ℚ → Choice.HistorySensitiveChoice) →
  ((h : History.History3) →
    decode (coarsePhotonMean detector h)
      ≡ Choice.historySensitiveChoice h) →
  ⊥
cannotRecoverHistoryChoiceFromOpticalMean detector decode adequate =
  Choice.abcAndAcbChoicesDiffer
    (trans
      (sym (adequate History.historyABC))
      (trans (cong decode (twoHistoriesOneOpticalMean detector))
             (adequate History.historyACB)))
  where
    open import Relation.Binary.PropositionalEquality using (trans; sym)

-- TSFV action candidates, phases, Gibbs weights, and MDL priors must
-- remain separate (TSFVActionPhaseWeightSeparationExact). This module
-- introduces no action/hbar or probability amplitude calibration.
