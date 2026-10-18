module DASHI.Biology.AvianMagnetoreceptionFieldObservationQuotientExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- FIELD OBSERVATION QUOTIENT
--
-- Exact finite witness of the inverse-problem boundary:
--
--   receptor-level exposure world -> chamber field observation
--
-- is not injective.  Two distinct receptor-exposure worlds may share the same
-- chamber measurement because tissue position/orientation/material context is
-- hidden by the measurement projection.
------------------------------------------------------------------------

data ChamberFieldObservation : Set where
  measuredFieldA : ChamberFieldObservation
  measuredFieldB : ChamberFieldObservation

data ReceptorExposureWorld : Set where
  superficialReceptorWorldA : ReceptorExposureWorld
  shieldedOrientedReceptorWorldA : ReceptorExposureWorld
  receptorWorldB : ReceptorExposureWorld

observeChamberField :
  ReceptorExposureWorld ->
  ChamberFieldObservation
observeChamberField superficialReceptorWorldA = measuredFieldA
observeChamberField shieldedOrientedReceptorWorldA = measuredFieldA
observeChamberField receptorWorldB = measuredFieldB

distinctExposureWorlds :
  superficialReceptorWorldA ≡ shieldedOrientedReceptorWorldA -> ⊥
distinctExposureWorlds ()

ChamberMeasurementDeterminesExactReceptorExposure : Set
ChamberMeasurementDeterminesExactReceptorExposure =
  (x y : ReceptorExposureWorld) ->
  observeChamberField x ≡ observeChamberField y ->
  x ≡ y

chamberMeasurementDoesNotDetermineExactReceptorExposure :
  ¬ ChamberMeasurementDeterminesExactReceptorExposure
chamberMeasurementDoesNotDetermineExactReceptorExposure exact =
  distinctExposureWorlds
    (exact
      superficialReceptorWorldA
      shieldedOrientedReceptorWorldA
      refl)

record SameChamberMeasurementCollision : Set where
  constructor same-chamber-measurement-collision
  field
    leftWorld : ReceptorExposureWorld
    rightWorld : ReceptorExposureWorld
    sameObservation :
      observeChamberField leftWorld ≡ observeChamberField rightWorld
    worldsDistinct :
      leftWorld ≡ rightWorld -> ⊥

open SameChamberMeasurementCollision public

canonicalSameChamberMeasurementCollision :
  SameChamberMeasurementCollision
canonicalSameChamberMeasurementCollision =
  same-chamber-measurement-collision
    superficialReceptorWorldA
    shieldedOrientedReceptorWorldA
    refl
    distinctExposureWorlds

------------------------------------------------------------------------
-- Synthesis is separately non-authoritative: a command labels an intended
-- apparatus state but does not prove the generated physical field.
------------------------------------------------------------------------

data ApparatusCommand : Set where
  commandA : ApparatusCommand
  commandB : ApparatusCommand

data GeneratedFieldWorld : Set where
  generatedNominalA : GeneratedFieldWorld
  generatedDistortedA : GeneratedFieldWorld
  generatedB : GeneratedFieldWorld

commandProjection : GeneratedFieldWorld -> ApparatusCommand
commandProjection generatedNominalA = commandA
commandProjection generatedDistortedA = commandA
commandProjection generatedB = commandB

distinctGeneratedWorlds :
  generatedNominalA ≡ generatedDistortedA -> ⊥
distinctGeneratedWorlds ()

CommandDeterminesExactGeneratedField : Set
CommandDeterminesExactGeneratedField =
  (x y : GeneratedFieldWorld) ->
  commandProjection x ≡ commandProjection y ->
  x ≡ y

commandDoesNotDetermineExactGeneratedField :
  ¬ CommandDeterminesExactGeneratedField
commandDoesNotDetermineExactGeneratedField exact =
  distinctGeneratedWorlds
    (exact generatedNominalA generatedDistortedA refl)

record FieldObservationQuotientBoundary : Set where
  constructor field-observation-quotient-boundary
  field
    commandDeterminesExactGeneratedField : Bool
    commandDeterminesExactGeneratedFieldIsFalse :
      commandDeterminesExactGeneratedField ≡ false

    chamberMeasurementDeterminesExactReceptorExposure : Bool
    chamberMeasurementDeterminesExactReceptorExposureIsFalse :
      chamberMeasurementDeterminesExactReceptorExposure ≡ false

    inverseProblemExplicit : Bool
    inverseProblemExplicitIsTrue :
      inverseProblemExplicit ≡ true

canonicalFieldObservationQuotientBoundary :
  FieldObservationQuotientBoundary
canonicalFieldObservationQuotientBoundary =
  field-observation-quotient-boundary
    false refl
    false refl
    true refl
