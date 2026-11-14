module DASHI.Reasoning.TrialecticC3GlobalNaturalityNoGoExact where

------------------------------------------------------------------------
-- C3 CHART ROTATION: GLOBAL NATURALITY NO-GO AND EXACT LOCAL REPAIR
--
-- The existing edge transport rotates one CellDialectic by
--
--   (left , right , synthesis) -> (right , synthesis , left).
--
-- On the canonical AB/BC/CA fixture this closes the expected C3 orbit.  It is
-- tempting to promote that edge transition to a natural C3 action on every
-- global T^18 boundary.  That promotion is too strong.
--
-- If AB->BC were globally natural with a vertex-local A->B map, then the old
-- B endpoint would have to be a function of the old A endpoint for every
-- compatible boundary.  But A and B are independent T^3 coordinates in the
-- exact six-cell chart.  We construct two compatible boundaries with the same
-- A and different B, then reuse ConsumerNonDescentWitness to prove the no-go.
--
-- The exact repair is also explicit: the full AB T^9 edge does determine B via
-- `rightCell`.  Thus any transport-enriched completion must retain richer local
-- context than one participant T^3 fibre, or restrict to a smaller subspace
-- such as the canonical orbit where additional equalities are supplied.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Core.Prelude using (⊥; cong; sym; trans)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ObserverFactorizedRefinementExact as Factorized
import DASHI.Core.RelationalTransportGroupoidActionExact as Groupoid
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Reasoning.TrialecticGrothendieckTransportCoherenceExact as Transport
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Cell

participantAObserver :
  Cell.CompatibleThreeCellTrialecticBoundary →
  Cell.TrialecticBasis3Cell
participantAObserver boundary =
  Cell.leftCell (Cell.edgeAB boundary)

participantBConsumer :
  Cell.CompatibleThreeCellTrialecticBoundary →
  Cell.TrialecticBasis3Cell
participantBConsumer boundary =
  Cell.rightCell (Cell.edgeAB boundary)

sameAFirstCoordinates : Cell.StructuredBoundaryCoordinates
sameAFirstCoordinates =
  Cell.structured-boundary-coordinates
    Fabric.negativeCorner
    Fabric.origin
    Fabric.positiveCorner
    Fabric.positiveCorner
    Fabric.negativeCorner
    Fabric.origin

sameASecondCoordinates : Cell.StructuredBoundaryCoordinates
sameASecondCoordinates =
  Cell.structured-boundary-coordinates
    Fabric.negativeCorner
    Fabric.positiveCorner
    Fabric.positiveCorner
    Fabric.positiveCorner
    Fabric.negativeCorner
    Fabric.origin

sameAFirstBoundary : Cell.CompatibleThreeCellTrialecticBoundary
sameAFirstBoundary =
  Cell.coordinatesToCompatibleBoundary sameAFirstCoordinates

sameASecondBoundary : Cell.CompatibleThreeCellTrialecticBoundary
sameASecondBoundary =
  Cell.coordinatesToCompatibleBoundary sameASecondCoordinates

sameParticipantA :
  participantAObserver sameAFirstBoundary
  ≡ participantAObserver sameASecondBoundary
sameParticipantA = refl

originNotPositiveCorner :
  Fabric.origin ≡ Fabric.positiveCorner → ⊥
originNotPositiveCorner equality with cong Fabric.x equality
... | ()

differentParticipantB :
  participantBConsumer sameAFirstBoundary
  ≡ participantBConsumer sameASecondBoundary →
  ⊥
differentParticipantB = originNotPositiveCorner

participantANonDescentWitnessForB :
  Descent.ConsumerNonDescentWitness
    participantAObserver
    participantBConsumer
participantANonDescentWitnessForB =
  Descent.consumerNonDescentWitness
    sameAFirstBoundary
    sameASecondBoundary
    sameParticipantA
    differentParticipantB

participantBCannotFactorThroughA :
  Descent.FactorsThrough participantAObserver participantBConsumer →
  ⊥
participantBCannotFactorThroughA =
  Descent.nonDescentWitnessBlocksFactorization
    participantANonDescentWitnessForB

participantBFactorsThroughABEdge :
  Descent.FactorsThrough Cell.edgeAB participantBConsumer
participantBFactorsThroughABEdge =
  Factorized.factorizedRefinement
    Cell.rightCell
    (λ boundary → refl)

record NaiveGlobalC3Naturality : Set₁ where
  constructor naive-global-c3-naturality
  field
    rotateGlobal :
      Cell.CompatibleThreeCellTrialecticBoundary →
      Cell.CompatibleThreeCellTrialecticBoundary

    rotateVertexAtoB :
      Cell.TrialecticBasis3Cell →
      Cell.TrialecticBasis3Cell

    abBecomesBC :
      (boundary : Cell.CompatibleThreeCellTrialecticBoundary) →
      Cell.edgeBC (rotateGlobal boundary)
      ≡ Transport.rotateCell (Cell.edgeAB boundary)

    vertexNaturality :
      (boundary : Cell.CompatibleThreeCellTrialecticBoundary) →
      Cell.leftCell (Cell.edgeBC (rotateGlobal boundary))
      ≡ rotateVertexAtoB (participantAObserver boundary)

open NaiveGlobalC3Naturality public

naiveC3NaturalityImpliesBFactorsThroughA :
  NaiveGlobalC3Naturality →
  Descent.FactorsThrough participantAObserver participantBConsumer
naiveC3NaturalityImpliesBFactorsThroughA candidate =
  Factorized.factorizedRefinement
    (rotateVertexAtoB candidate)
    factorizes
  where
    factorizes :
      (boundary : Cell.CompatibleThreeCellTrialecticBoundary) →
      participantBConsumer boundary
      ≡ rotateVertexAtoB candidate (participantAObserver boundary)
    factorizes boundary =
      trans
        (sym (cong Cell.leftCell (abBecomesBC candidate boundary)))
        (vertexNaturality candidate boundary)

naiveGlobalC3NaturalityImpossible :
  NaiveGlobalC3Naturality → ⊥
naiveGlobalC3NaturalityImpossible candidate =
  participantBCannotFactorThroughA
    (naiveC3NaturalityImpliesBFactorsThroughA candidate)

canonicalABStillRotatesToBC :
  Groupoid.forward Transport.transportABtoBC Cell.canonicalCellAB
  ≡ Cell.canonicalCellBC
canonicalABStillRotatesToBC = Transport.canonicalABtoBC

record TrialecticC3GlobalNaturalityNoGoBoundary : Set where
  constructor trialectic-c3-global-naturality-no-go-boundary
  field
    participantANotSufficientForB : Bool
    fullABEdgeSufficientForB : Bool
    canonicalC3EdgeOrbitRetained : Bool
    naiveGlobalC3NaturalityPaid : Bool
    richerLocalContextRequired : Bool
    canonicalOrbitAutomaticallyExtendsToAllT18States : Bool

open TrialecticC3GlobalNaturalityNoGoBoundary public

canonicalTrialecticC3GlobalNaturalityNoGoBoundary :
  TrialecticC3GlobalNaturalityNoGoBoundary
canonicalTrialecticC3GlobalNaturalityNoGoBoundary =
  trialectic-c3-global-naturality-no-go-boundary
    true true true false true false
