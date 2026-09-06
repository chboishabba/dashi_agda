module DASHI.Core.QueryFibreAddedCoordinateProducerBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.QueryCompatibleFibreConsumerClosureBidiExact as Query
import DASHI.Core.BidiResidualApproximationExact as Bidi
import DASHI.Core.ExperimentalCoordinateDesignExact as Design

------------------------------------------------------------------------
-- QUERY FIBRE COLLISION -> ADDED COORDINATE PRODUCER
--
-- A current query may close its own consumer while leaving distinct compatible
-- hidden worlds.  If a later consumer needs one of those hidden distinctions,
-- the repair is an added observation coordinate carrying an actual separation
-- witness, not a relabelling of the old query result.
------------------------------------------------------------------------

record QueryFibreCollision
    {QueryT State Hidden Answer : Set}
    (problem : Query.QueryCompatibleProblem QueryT State Hidden Answer)
    (query : QueryT)
    (state : State) : Set where
  constructor query-fibre-collision
  field
    left right : Hidden
    leftCompatible : Query.compatible problem query state left
    rightCompatible : Query.compatible problem query state right
    sameCurrentAnswer :
      Query.consumer problem query left ≡ Query.consumer problem query right
    hiddenDifference : left ≡ right → ⊥

open QueryFibreCollision public

record AddedCoordinateProducer
    {QueryT State Hidden Answer Control Value Dimension ExistingCode : Set}
    {problem : Query.QueryCompatibleProblem QueryT State Hidden Answer}
    {query : QueryT} {state : State}
    (collision : QueryFibreCollision problem query state)
    (design : Design.ExperimentalCoordinateDesign Hidden Control Value Dimension)
    (existing : Hidden → ExistingCode) : Set₁ where
  constructor added-coordinate-producer
  field
    separator : Design.CoordinateSeparatesCollision design existing
    separatorLeftMatches : Design.left separator ≡ left collision
    separatorRightMatches : Design.right separator ≡ right collision
    producerReference : String
    calibrationReference : String

open AddedCoordinateProducer public

MeasuredQueryFibre :
  ∀ {QueryT State Hidden Answer Control Value Dimension : Set} →
  (problem : Query.QueryCompatibleProblem QueryT State Hidden Answer) →
  (query : QueryT) → (state : State) →
  (design : Design.ExperimentalCoordinateDesign Hidden Control Value Dimension) →
  Design.Coordinate design → Value →
  Bidi.ResidualFibre Hidden
MeasuredQueryFibre problem query state design coordinate observed =
  Bidi.MeasuredFibre
    (Query.queryResidualFibre problem query state)
    (Design.read design coordinate)
    observed

addedCoordinateAlwaysRefinesQueryFibre :
  ∀ {QueryT State Hidden Answer Control Value Dimension : Set}
    (problem : Query.QueryCompatibleProblem QueryT State Hidden Answer)
    (query : QueryT) (state : State)
    (design : Design.ExperimentalCoordinateDesign Hidden Control Value Dimension)
    (coordinate : Design.Coordinate design)
    (observed : Value) →
  Bidi.FibreRefines
    (MeasuredQueryFibre problem query state design coordinate observed)
    (Query.queryResidualFibre problem query state)
addedCoordinateAlwaysRefinesQueryFibre problem query state design coordinate observed =
  Bidi.measurementAlwaysRefinesPrior
    (Query.queryResidualFibre problem query state)
    (Design.read design coordinate)
    observed

------------------------------------------------------------------------
-- No-collapse boundaries.
------------------------------------------------------------------------

data NamingCoordinateSeparatesCollision : Set where
data ConsumerClosureMeansNoFutureCoordinateCanHelp : Set where
data AddedCoordinateAutomaticallyIdentifiesMechanism : Set where

namingCoordinateDoesNotSeparateCollision : NamingCoordinateSeparatesCollision → ⊥
namingCoordinateDoesNotSeparateCollision ()

consumerClosureDoesNotBlockFutureUsefulCoordinates :
  ConsumerClosureMeansNoFutureCoordinateCanHelp → ⊥
consumerClosureDoesNotBlockFutureUsefulCoordinates ()

addedCoordinateDoesNotAutomaticallyIdentifyMechanism :
  AddedCoordinateAutomaticallyIdentifiesMechanism → ⊥
addedCoordinateDoesNotAutomaticallyIdentifyMechanism ()

record QueryFibreCoordinateBoundary : Set where
  constructor query-fibre-coordinate-boundary
  field
    addedCoordinateNeedsSeparationWitness : Bool
    measuredCoordinateRefinesCompatibleFibre : Bool
    closedCurrentConsumerEndsAllInquiry : Bool
    coordinateSeparationIsMechanismIdentification : Bool

canonicalQueryFibreCoordinateBoundary : QueryFibreCoordinateBoundary
canonicalQueryFibreCoordinateBoundary =
  query-fibre-coordinate-boundary true true false false
