module DASHI.Physics.Foundations.StationaryCoherenceClassificationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Stationarity is the primitive first-variation notion.  Minimum, maximum,
-- saddle, degenerate stationary point, and metric-shortest are separate
-- classifications/claims.
------------------------------------------------------------------------

data StationarySecondVariationClass : Set where
  localMinimumClass : StationarySecondVariationClass
  localMaximumClass : StationarySecondVariationClass
  saddleClass : StationarySecondVariationClass
  degenerateClass : StationarySecondVariationClass

data StationaryWitnessKind : Set where
  firstOrderStationary : StationaryWitnessKind
  firstOrderNonstationary : StationaryWitnessKind

data MetricShortestStatus : Set where
  metricShortest : MetricShortestStatus
  notMetricShortest : MetricShortestStatus
  metricShortestUnresolved : MetricShortestStatus

record StationaryCoherenceSurface : Set₁ where
  field
    VariationFamily : Set
    ActionValue : Set
    PhaseValue : Set

    actionOf : VariationFamily → ActionValue
    phaseOf : VariationFamily → PhaseValue
    stationaryKind : VariationFamily → StationaryWitnessKind
    secondVariationClass : VariationFamily → StationarySecondVariationClass
    metricShortestStatus : VariationFamily → MetricShortestStatus

    firstOrderCoherenceLaw : VariationFamily → Set
    firstOrderCoherenceAtStationary :
      (variation : VariationFamily) →
      stationaryKind variation ≡ firstOrderStationary →
      firstOrderCoherenceLaw variation

    surfaceReading : String

open StationaryCoherenceSurface public

data ToyVariation : Set where
  minimumStationaryVariation : ToyVariation
  saddleStationaryVariation : ToyVariation
  nonstationaryVariation : ToyVariation

data ToyAction : Set where
  actionA : ToyAction
  actionB : ToyAction
  actionC : ToyAction

data ToyPhase : Set where
  phaseA : ToyPhase
  phaseB : ToyPhase
  phaseC : ToyPhase

data ToyCoherence : ToyVariation → Set where
  minimumCoherent : ToyCoherence minimumStationaryVariation
  saddleCoherent : ToyCoherence saddleStationaryVariation

canonicalStationaryCoherenceSurface : StationaryCoherenceSurface
canonicalStationaryCoherenceSurface =
  record
    { VariationFamily = ToyVariation
    ; ActionValue = ToyAction
    ; PhaseValue = ToyPhase
    ; actionOf = λ
        { minimumStationaryVariation → actionA
        ; saddleStationaryVariation → actionB
        ; nonstationaryVariation → actionC
        }
    ; phaseOf = λ
        { minimumStationaryVariation → phaseA
        ; saddleStationaryVariation → phaseB
        ; nonstationaryVariation → phaseC
        }
    ; stationaryKind = λ
        { minimumStationaryVariation → firstOrderStationary
        ; saddleStationaryVariation → firstOrderStationary
        ; nonstationaryVariation → firstOrderNonstationary
        }
    ; secondVariationClass = λ
        { minimumStationaryVariation → localMinimumClass
        ; saddleStationaryVariation → saddleClass
        ; nonstationaryVariation → degenerateClass
        }
    ; metricShortestStatus = λ
        { minimumStationaryVariation → metricShortestUnresolved
        ; saddleStationaryVariation → notMetricShortest
        ; nonstationaryVariation → metricShortestUnresolved
        }
    ; firstOrderCoherenceLaw = ToyCoherence
    ; firstOrderCoherenceAtStationary = λ
        { minimumStationaryVariation refl → minimumCoherent
        ; saddleStationaryVariation refl → saddleCoherent
        ; nonstationaryVariation ()
        }
    ; surfaceReading =
        "First-order stationary coherence is typed separately from second-variation class and metric-shortest status."
    }

stationaryCanBeMinimum :
  stationaryKind canonicalStationaryCoherenceSurface minimumStationaryVariation
  ≡ firstOrderStationary
  ×
  secondVariationClass canonicalStationaryCoherenceSurface minimumStationaryVariation
  ≡ localMinimumClass
stationaryCanBeMinimum = refl , refl

stationaryCanBeSaddle :
  stationaryKind canonicalStationaryCoherenceSurface saddleStationaryVariation
  ≡ firstOrderStationary
  ×
  secondVariationClass canonicalStationaryCoherenceSurface saddleStationaryVariation
  ≡ saddleClass
stationaryCanBeSaddle = refl , refl

stationaryDoesNotDetermineMinimumClass :
  secondVariationClass canonicalStationaryCoherenceSurface saddleStationaryVariation
  ≡ localMinimumClass → ⊥
stationaryDoesNotDetermineMinimumClass ()

stationaryDoesNotDetermineMetricShortest :
  metricShortestStatus canonicalStationaryCoherenceSurface saddleStationaryVariation
  ≡ metricShortest → ⊥
stationaryDoesNotDetermineMetricShortest ()

record StationaryCoherenceNonPromotionBoundary : Set where
  constructor stationaryCoherenceNonPromotionBoundary
  field
    stationaryMeansMinimum : Bool
    stationaryMeansMinimumIsFalse : stationaryMeansMinimum ≡ false

    stationaryMeansMetricShortest : Bool
    stationaryMeansMetricShortestIsFalse :
      stationaryMeansMetricShortest ≡ false

    finiteStationaryWitnessProvesContinuumLimit : Bool
    finiteStationaryWitnessProvesContinuumLimitIsFalse :
      finiteStationaryWitnessProvesContinuumLimit ≡ false

canonicalStationaryCoherenceNonPromotionBoundary :
  StationaryCoherenceNonPromotionBoundary
canonicalStationaryCoherenceNonPromotionBoundary =
  stationaryCoherenceNonPromotionBoundary
    false refl
    false refl
    false refl
