module DASHI.Physics.Closure.TSFVBidirectionalCausticBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.BidirectionallyAdmissibleHistoryFibreExact as Bidi
import DASHI.Physics.Foundations.TrajectoryProjectionCausticExact as Caustic
import DASHI.Physics.Foundations.FiniteHistoryFunctionalExact as History
import DASHI.Physics.Foundations.PathIntegralExperimentalSourceRegistryExact as Sources
import DASHI.Physics.Foundations.StationaryCoherenceClassificationExact as Stationary
import DASHI.Physics.Closure.FeynmanKelvinTrajectoryCrossPollinationExact as FeynmanKelvin
import DASHI.Physics.Closure.QuantumPathFibreObservationQuotient as Quantum
import DASHI.Physics.Closure.TSFVCandidate256CalibrationLawDiagnostic as TSFV
import DASHI.Physics.Closure.W4SurrogateScaleSettingBoundary as Surrogate

------------------------------------------------------------------------
-- Repo-native TSFV ordering:
--
--   two-boundary compatibility
--     -> admissible history fibre
--     -> invariant/equivalence structure
--     -> weighting / action / phase
--     -> projection criticality / caustic
--     -> observation quotient
--
-- The projection layer is therefore downstream of admissibility.  It cannot
-- retroactively define which histories were admissible.
------------------------------------------------------------------------

historyBidirectionalSurface : Bidi.BidirectionallyAdmissibleHistoryFibre
historyBidirectionalSurface =
  record
    { InitialBoundary = History.InitialBoundary
    ; FinalBoundary = History.FinalBoundary
    ; History = History.History3
    ; admissibleFromBoth = λ initial final history →
        History.compatibleWithBoundaries initial final history
        ≡ History.compatible
    ; fibreReading =
        "FiniteHistoryFunctionalExact supplies a concrete two-boundary history fibre: compatibility with initial and final boundaries is checked before downstream projection or observation."
    }

historyPruningIsBidirectionallyAdmissible :
  (final : History.FinalBoundary) →
  Bidi.admissibleFromBoth
    historyBidirectionalSurface
    History.initialA
    final
    (History.prunedHistory final)
historyPruningIsBidirectionallyAdmissible =
  History.pruningSelectsCompatibleHistory

------------------------------------------------------------------------
-- Finite projection specimen over the existing History3 carrier.
------------------------------------------------------------------------

data HistoryObservation : Set where
  focusedHistoryObservation : HistoryObservation
  diffuseHistoryObservation : HistoryObservation

data HistoryStationary : History.History3 → Set where
  historyABCStationary : HistoryStationary History.historyABC

data HistoryProjectionCritical : History.History3 → Set where
  historyACBProjectionCritical :
    HistoryProjectionCritical History.historyACB

data HistorySourceWeighted : History.History3 → Set where
  historyABCWeighted : HistorySourceWeighted History.historyABC
  historyACBWeighted : HistorySourceWeighted History.historyACB

data HistoryCoherentlyEnhanced : HistoryObservation → Set where
  focusedHistoryEnhanced :
    HistoryCoherentlyEnhanced focusedHistoryObservation

data HistoryCausticObservation : HistoryObservation → Set where
  focusedHistoryCaustic :
    HistoryCausticObservation focusedHistoryObservation

historyProjection : History.History3 → HistoryObservation
historyProjection (History.configurationA , (History.configurationB , History.configurationC)) =
  focusedHistoryObservation
historyProjection (History.configurationA , (History.configurationC , History.configurationB)) =
  focusedHistoryObservation
historyProjection history = diffuseHistoryObservation

historyTrajectoryProjectionCaustic :
  Caustic.TrajectoryProjectionCaustic historyBidirectionalSurface
historyTrajectoryProjectionCaustic =
  record
    { Observation = HistoryObservation
    ; project = historyProjection
    ; StationaryAction = HistoryStationary
    ; ProjectionCritical = HistoryProjectionCritical
    ; SourceWeighted = HistorySourceWeighted
    ; CoherentlyEnhanced = HistoryCoherentlyEnhanced
    ; CausticObservation = HistoryCausticObservation
    ; projectionReading =
        "Two boundary-compatible finite histories may share one coarse observation; the toy witness separates stationary action, projection criticality, weighting, enhancement and caustic classification."
    }

historyABCAndACBAreDistinct :
  History.historyABC ≡ History.historyACB → ⊥
historyABCAndACBAreDistinct ()

historyDistinctSharedProjection :
  Caustic.DistinctHistoriesSharedProjection historyTrajectoryProjectionCaustic
historyDistinctSharedProjection =
  record
    { historyLeft = History.historyABC
    ; historyRight = History.historyACB
    ; historiesDistinct = historyABCAndACBAreDistinct
    ; sharedProjection = refl
    }

------------------------------------------------------------------------
-- Existing TSFV representative/invariant machinery remains upstream of the
-- observational interpretation.  This is structural reuse, not experimental
-- validation of TSFV.
------------------------------------------------------------------------

tsfvRepresentativeInvolution :
  (q : Surrogate.Candidate256QuotientClass) →
  TSFV.candidate256QuotientT (TSFV.candidate256QuotientT q) ≡ q
tsfvRepresentativeInvolution =
  TSFV.candidate256QuotientTInvolutive

tsfvCalibrationInvariant :
  (q : Surrogate.Candidate256QuotientClass) →
  TSFV.candidate256TritQuotientCalibrationMap
    (TSFV.candidate256QuotientT q)
  ≡ TSFV.candidate256TritQuotientCalibrationMap q
tsfvCalibrationInvariant =
  TSFV.candidate256TritDimensionalInvarianceUnderT

------------------------------------------------------------------------
-- Aggregate bridge and claim boundary.
------------------------------------------------------------------------

record TSFVBidirectionalCausticBridge : Set₁ where
  field
    bidiSurface : Bidi.BidirectionallyAdmissibleHistoryFibre
    projectionSurface : Caustic.TrajectoryProjectionCaustic bidiSurface

    bidiBoundary : Bidi.BidirectionalAdmissibilityBoundary
    causticBoundary : Caustic.ProjectionCausticBoundary
    stationaryBoundary : Stationary.StationaryCoherenceNonPromotionBoundary

    quantumObservationSurface : Quantum.QuantumPathFibreObservationQuotient
    feynmanKelvinSurface : FeynmanKelvin.FeynmanKelvinTrajectoryBridge

    catastropheOpticsSource : Sources.SourceReference
    causticSingularitySource : Sources.SourceReference

    projectionDefinesAdmissibility : Bool
    projectionDefinesAdmissibilityIsFalse :
      projectionDefinesAdmissibility ≡ false

    sharpObservationImpliesUniqueHistory : Bool
    sharpObservationImpliesUniqueHistoryIsFalse :
      sharpObservationImpliesUniqueHistory ≡ false

    bidiCompatibilityImpliesRetrocausalSignal : Bool
    bidiCompatibilityImpliesRetrocausalSignalIsFalse :
      bidiCompatibilityImpliesRetrocausalSignal ≡ false

    causticIsStationaryMinimum : Bool
    causticIsStationaryMinimumIsFalse :
      causticIsStationaryMinimum ≡ false

    photonExperimentValidatesTSFVCausticMechanism : Bool
    photonExperimentValidatesTSFVCausticMechanismIsFalse :
      photonExperimentValidatesTSFVCausticMechanism ≡ false

    bridgeReading : String

open TSFVBidirectionalCausticBridge public

canonicalTSFVBidirectionalCausticBridge : TSFVBidirectionalCausticBridge
canonicalTSFVBidirectionalCausticBridge =
  record
    { bidiSurface = historyBidirectionalSurface
    ; projectionSurface = historyTrajectoryProjectionCaustic
    ; bidiBoundary = Bidi.canonicalBidirectionalAdmissibilityBoundary
    ; causticBoundary = Caustic.canonicalProjectionCausticBoundary
    ; stationaryBoundary = Stationary.canonicalStationaryCoherenceNonPromotionBoundary
    ; quantumObservationSurface =
        Quantum.canonicalQuantumPathFibreObservationQuotient
    ; feynmanKelvinSurface =
        FeynmanKelvin.canonicalFeynmanKelvinTrajectoryBridge
    ; catastropheOpticsSource = Sources.berryUpstill1980
    ; causticSingularitySource = Sources.arnold1990Caustics
    ; projectionDefinesAdmissibility = false
    ; projectionDefinesAdmissibilityIsFalse = refl
    ; sharpObservationImpliesUniqueHistory = false
    ; sharpObservationImpliesUniqueHistoryIsFalse = refl
    ; bidiCompatibilityImpliesRetrocausalSignal = false
    ; bidiCompatibilityImpliesRetrocausalSignalIsFalse = refl
    ; causticIsStationaryMinimum = false
    ; causticIsStationaryMinimumIsFalse = refl
    ; photonExperimentValidatesTSFVCausticMechanism = false
    ; photonExperimentValidatesTSFVCausticMechanismIsFalse = refl
    ; bridgeReading =
        "TSFV-native ordering begins with bidirectional boundary compatibility and admissible history fibres; invariant structure, weighting, stationarity, projection criticality and caustic observation are downstream, and a sharp coarse feature need not identify one microscopic history."
    }
