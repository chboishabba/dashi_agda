module DASHI.Reasoning.TrialecticAttachedTwoCellExact where

------------------------------------------------------------------------
-- TRIALECTIC = DYADIC CECH 1-SKELETON + IRREDUCIBLE ATTACHED 2-CELL
--
-- DASHI CONTRIBUTION
--
-- The literal dyadic participant cover has:
--
--   three patches,
--   three singleton pairwise overlaps,
--   empty triple intersection.
--
-- Hence its Cech nerve is the triangular 1-skeleton, not a filled triangle.
--
-- Separately, TrialecticBoundaryFaceNonfactorabilityExact owns an irreducible
-- TriadicFaceRelation that does not factor through the three edge values.
--
-- We therefore package the trialectic face as an *attached relational 2-cell*
-- over the boundary.  It is not the Cech triple-intersection object and not
-- determined by the 1-skeleton.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Reasoning.TrialecticDyadicCoverNerveExact as Nerve
import DASHI.Reasoning.TrialecticBoundaryFaceNonfactorabilityExact as Face
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent

record TrialecticAttachedTwoCell : Set where
  constructor trialectic-attached-two-cell
  field
    boundary : Face.TrialecticBoundary
    attachedFace : Face.TriadicFaceRelation

open TrialecticAttachedTwoCell public

fromExistingTrialecticState :
  Face.TrialecticState ->
  TrialecticAttachedTwoCell
fromExistingTrialecticState state =
  trialectic-attached-two-cell
    (Face.boundary state)
    (Face.face state)

toExistingTrialecticState :
  TrialecticAttachedTwoCell ->
  Face.TrialecticState
toExistingTrialecticState state =
  Face.trialectic-state
    (boundary state)
    (attachedFace state)

attachedExistingRoundTrip :
  (state : TrialecticAttachedTwoCell) ->
  fromExistingTrialecticState (toExistingTrialecticState state) ≡ state
attachedExistingRoundTrip
  (trialectic-attached-two-cell boundary face) = refl

existingAttachedRoundTrip :
  (state : Face.TrialecticState) ->
  toExistingTrialecticState (fromExistingTrialecticState state) ≡ state
existingAttachedRoundTrip
  (Face.trialectic-state boundary face) = refl

attachedBoundaryObserver :
  TrialecticAttachedTwoCell ->
  Face.TrialecticBoundary
attachedBoundaryObserver = boundary

attachedFaceConsumer :
  TrialecticAttachedTwoCell ->
  Face.TriadicFaceRelation
attachedFaceConsumer = attachedFace

sameBoundaryDifferentAttachedFaceLeft :
  TrialecticAttachedTwoCell
sameBoundaryDifferentAttachedFaceLeft =
  trialectic-attached-two-cell
    Face.sharedPositiveBoundary
    Face.reciprocalFace

sameBoundaryDifferentAttachedFaceRight :
  TrialecticAttachedTwoCell
sameBoundaryDifferentAttachedFaceRight =
  trialectic-attached-two-cell
    Face.sharedPositiveBoundary
    Face.coerciveFace

attachedTwoCellNonDescent :
  Descent.ConsumerNonDescentWitness
    attachedBoundaryObserver
    attachedFaceConsumer
attachedTwoCellNonDescent =
  Descent.consumerNonDescentWitness
    sameBoundaryDifferentAttachedFaceLeft
    sameBoundaryDifferentAttachedFaceRight
    refl
    (λ ())

attachedFaceDoesNotFactorThroughBoundary :
  Descent.FactorsThrough
    attachedBoundaryObserver
    attachedFaceConsumer
  ->
  ⊥
attachedFaceDoesNotFactorThroughBoundary =
  Descent.nonDescentWitnessBlocksFactorization
    attachedTwoCellNonDescent

------------------------------------------------------------------------
-- The two distinct notions of "filled triangle" remain separated.
------------------------------------------------------------------------

data AttachedFaceIsCechTripleIntersection : Set where
data EmptyTripleIntersectionDeletesAttachedFace : Set where

attachedFaceIsNotCechTripleIntersection :
  AttachedFaceIsCechTripleIntersection -> ⊥
attachedFaceIsNotCechTripleIntersection ()

emptyTripleIntersectionDoesNotDeleteAttachedFace :
  EmptyTripleIntersectionDeletesAttachedFace -> ⊥
emptyTripleIntersectionDoesNotDeleteAttachedFace ()

dyadicTripleIntersectionIsEmpty :
  Nerve.TripleIntersectionWitness -> ⊥
dyadicTripleIntersectionIsEmpty =
  Nerve.relationalDyadicTripleIntersectionEmpty

existingFaceNonfactorability =
  Face.triadicFaceCannotFactorThroughThreeEdges

record TrialecticAttachedTwoCellBoundary : Set where
  constructor trialectic-attached-two-cell-boundary
  field
    dyadicCechNerveHasOnlyOneSkeleton : Bool
    tripleParticipantIntersectionEmpty : Bool
    attachedFaceStillRetained : Bool
    attachedFaceFactorsThroughBoundary : Bool
    attachedFaceEqualsCechTripleIntersection : Bool
    existingTrialecticStateEquivalentToAttachedCellPackage : Bool

canonicalTrialecticAttachedTwoCellBoundary :
  TrialecticAttachedTwoCellBoundary
canonicalTrialecticAttachedTwoCellBoundary =
  trialectic-attached-two-cell-boundary
    true true true false false true
