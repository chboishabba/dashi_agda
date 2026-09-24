module DASHI.Core.ObjectDecompositionResidualRouterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- DEPENDENT OBJECT DECOMPOSITION / REVERSE-ACQUISITION ROUTER
--
-- This is a thin generic shell over the many existing domain owners whose
-- objects already expose process stages, parts, mechanisms, measurements,
-- provenance and reverse/BIDI acquisition targets.  It does not create a new
-- universal ontology.  A domain supplies only the coordinates relevant to its
-- own object type and consumer.
------------------------------------------------------------------------

data CoordinateStatus : Set where
  paidCoordinate
  partialCoordinate
  unresolvedCoordinate
  inapplicableCoordinate :
    CoordinateStatus

record ObjectDecompositionSystem
    (Object Consumer : Set) : Set₁ where
  constructor object-decomposition-system
  field
    Coordinate : Object → Set
    Value :
      (object : Object) →
      Coordinate object →
      Set

    status :
      (object : Object) →
      (coordinate : Coordinate object) →
      CoordinateStatus

    requiredBy :
      Consumer →
      (object : Object) →
      Coordinate object →
      Set

    ownerReference :
      (object : Object) →
      (coordinate : Coordinate object) →
      String

    reverseAcquisitionReference :
      Consumer →
      (object : Object) →
      (coordinate : Coordinate object) →
      String

open ObjectDecompositionSystem public

record ConsumerRelevantObjectResidual
    {Object Consumer : Set}
    (system : ObjectDecompositionSystem Object Consumer) : Set₁ where
  constructor consumer-relevant-object-residual
  field
    consumer : Consumer
    object : Object
    coordinate : Coordinate system object
    required : requiredBy system consumer object coordinate
    currentStatus : CoordinateStatus
    currentStatusMatches : currentStatus ≡ status system object coordinate
    domainOwnerReference : String
    reverseTargetReference : String
    answerChangingReference : String

open ConsumerRelevantObjectResidual public

record ObjectResidualSearchIntent
    {Object Consumer : Set}
    {system : ObjectDecompositionSystem Object Consumer}
    (residual : ConsumerRelevantObjectResidual system) : Set where
  constructor object-residual-search-intent
  field
    expectedPropositionShape : String
    supportingProbeReference : String
    defeaterProbeReference : String
    comparatorProbeReference : String
    contradictionProbeReference : String
    providerNeutralQueryReference : String
    searchOnlyIfUnresolvedOrPartial : Bool
    searchOnlyIfUnresolvedOrPartialIsTrue :
      searchOnlyIfUnresolvedOrPartial ≡ true

open ObjectResidualSearchIntent public

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record ObjectDecompositionResidualBoundary : Set where
  constructor object-decomposition-residual-boundary
  field
    oneUniversalCartesianOntologyRequired : Bool
    oneUniversalCartesianOntologyRequiredIsFalse :
      oneUniversalCartesianOntologyRequired ≡ false

    nominalObjectLabelDeterminesLifecycleStage : Bool
    nominalObjectLabelDeterminesLifecycleStageIsFalse :
      nominalObjectLabelDeterminesLifecycleStage ≡ false

    everyUnknownCoordinateMustBeAcquired : Bool
    everyUnknownCoordinateMustBeAcquiredIsFalse :
      everyUnknownCoordinateMustBeAcquired ≡ false

    consumerRequirementControlsReverseSearch : Bool
    consumerRequirementControlsReverseSearchIsTrue :
      consumerRequirementControlsReverseSearch ≡ true

    domainOwnerRemainsAuthority : Bool
    domainOwnerRemainsAuthorityIsTrue :
      domainOwnerRemainsAuthority ≡ true

canonicalObjectDecompositionResidualBoundary :
  ObjectDecompositionResidualBoundary
canonicalObjectDecompositionResidualBoundary =
  object-decomposition-residual-boundary
    false refl
    false refl
    false refl
    true refl
    true refl
