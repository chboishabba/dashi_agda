module DASHI.Physics.Foundations.TrajectoryProjectionCausticExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.BidirectionallyAdmissibleHistoryFibreExact as Bidi

------------------------------------------------------------------------
-- Projection / caustic layer downstream of bidirectional admissibility.
--
-- A caustic is represented here only as a typed projection-critical / focused
-- observation structure.  This finite exact owner does not pretend to encode
-- differential Jacobians or continuum catastrophe theory.  Analytic consumers
-- may later supply derivative/Hessian/Jacobian receipts.
------------------------------------------------------------------------

record TrajectoryProjectionCaustic
    (bidi : Bidi.BidirectionallyAdmissibleHistoryFibre) : Set₁ where
  field
    Observation : Set

    project : Bidi.History bidi → Observation

    StationaryAction : Bidi.History bidi → Set
    ProjectionCritical : Bidi.History bidi → Set
    SourceWeighted : Bidi.History bidi → Set
    CoherentlyEnhanced : Observation → Set
    CausticObservation : Observation → Set

    projectionReading : String

open TrajectoryProjectionCaustic public

------------------------------------------------------------------------
-- Focus witness: two distinct fine histories can share one coarse projection.
-- This is the exact finite analogue needed for the "many representatives ->
-- one sharp feature" boundary without claiming a continuum caustic theorem.
------------------------------------------------------------------------

record DistinctHistoriesSharedProjection
    {bidi : Bidi.BidirectionallyAdmissibleHistoryFibre}
    (surface : TrajectoryProjectionCaustic bidi) : Set where
  field
    historyLeft : Bidi.History bidi
    historyRight : Bidi.History bidi

    historiesDistinct : historyLeft ≡ historyRight → ⊥

    sharedProjection :
      project surface historyLeft ≡ project surface historyRight

open DistinctHistoriesSharedProjection public

data ToyObservation : Set where
  focusedObservation : ToyObservation
  diffuseObservation : ToyObservation

data ToyStationary : Bidi.ToyHistory → Set where
  leftStationary : ToyStationary Bidi.leftCompatibleHistory

data ToyProjectionCritical : Bidi.ToyHistory → Set where
  rightProjectionCritical :
    ToyProjectionCritical Bidi.rightCompatibleHistory

data ToySourceWeighted : Bidi.ToyHistory → Set where
  leftStronglyWeighted : ToySourceWeighted Bidi.leftCompatibleHistory
  rightStronglyWeighted : ToySourceWeighted Bidi.rightCompatibleHistory

data ToyEnhanced : ToyObservation → Set where
  focusedEnhanced : ToyEnhanced focusedObservation

data ToyCaustic : ToyObservation → Set where
  focusedCaustic : ToyCaustic focusedObservation

canonicalTrajectoryProjectionCaustic :
  TrajectoryProjectionCaustic Bidi.canonicalBidirectionallyAdmissibleHistoryFibre
canonicalTrajectoryProjectionCaustic =
  record
    { Observation = ToyObservation
    ; project = λ
        { Bidi.leftCompatibleHistory → focusedObservation
        ; Bidi.rightCompatibleHistory → focusedObservation
        ; Bidi.incompatibleHistory → diffuseObservation
        }
    ; StationaryAction = ToyStationary
    ; ProjectionCritical = ToyProjectionCritical
    ; SourceWeighted = ToySourceWeighted
    ; CoherentlyEnhanced = ToyEnhanced
    ; CausticObservation = ToyCaustic
    ; projectionReading =
        "Projection criticality and caustic observation are downstream of the bidirectionally admissible history fibre and remain distinct from stationary action and source weighting."
    }

canonicalDistinctHistoriesSharedProjection :
  DistinctHistoriesSharedProjection canonicalTrajectoryProjectionCaustic
canonicalDistinctHistoriesSharedProjection =
  record
    { historyLeft = Bidi.leftCompatibleHistory
    ; historyRight = Bidi.rightCompatibleHistory
    ; historiesDistinct = Bidi.leftAndRightCompatibleHistoriesAreDistinct
    ; sharedProjection = refl
    }

------------------------------------------------------------------------
-- Exact non-collapse boundaries.
------------------------------------------------------------------------

record ProjectionCausticBoundary : Set where
  constructor projectionCausticBoundary
  field
    stationaryActionIsProjectionCriticality : Bool
    stationaryActionIsProjectionCriticalityIsFalse :
      stationaryActionIsProjectionCriticality ≡ false

    projectionCriticalityIsSourceWeighting : Bool
    projectionCriticalityIsSourceWeightingIsFalse :
      projectionCriticalityIsSourceWeighting ≡ false

    causticMeansMinimumAction : Bool
    causticMeansMinimumActionIsFalse :
      causticMeansMinimumAction ≡ false

    causticMeansUniqueMicroscopicHistory : Bool
    causticMeansUniqueMicroscopicHistoryIsFalse :
      causticMeansUniqueMicroscopicHistory ≡ false

    sharedProjectionMeansIdenticalHistory : Bool
    sharedProjectionMeansIdenticalHistoryIsFalse :
      sharedProjectionMeansIdenticalHistory ≡ false

canonicalProjectionCausticBoundary : ProjectionCausticBoundary
canonicalProjectionCausticBoundary =
  projectionCausticBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
