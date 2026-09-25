module DASHI.Core.ProvenancePreservingRecognitionFunctorExact where

------------------------------------------------------------------------
-- PROVENANCE-PRESERVING RECOGNITION
--
-- DASHI CONTRIBUTION
--
-- Refines ActionOrbitRecognitionFunctorExact with a second, independent
-- requirement: recognition must preserve the source's provenance/history
-- coordinate.  Shared observations, equal orbit labels, or an equivariant
-- state map do not by themselves license provenance fusion.
--
-- This is motivated structurally by existing Two-Eyed Seeing / Sweetgrass
-- owners, but the finite contract below is repository mathematics and is not
-- attributed to those sources.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ResidualSymmetryCollisionFibreExact as Action
import DASHI.Core.OrbitStabilizerResidualPresentationExact as Orbit
import DASHI.Core.ActionOrbitRecognitionFunctorExact as Recognition

record ProvenancePreservingActionRecognition
    {SourceState SourceSymmetry TargetState TargetSymmetry : Set}
    {SourceProvenance TargetProvenance : Set}
    (sourceAction :
      Action.InvertibleSymmetryAction SourceState SourceSymmetry)
    (targetAction :
      Action.InvertibleSymmetryAction TargetState TargetSymmetry)
    (sourceProvenance : SourceState -> SourceProvenance)
    (targetProvenance : TargetState -> TargetProvenance) : Set₁ where
  constructor provenance-preserving-action-recognition
  field
    actionRecognition :
      Recognition.ActionRecognitionFunctor sourceAction targetAction

    mapProvenance :
      SourceProvenance -> TargetProvenance

    provenanceCommutes :
      (state : SourceState) ->
      targetProvenance
        (Recognition.mapState actionRecognition state)
      ≡
      mapProvenance (sourceProvenance state)

    reflectsMappedProvenance :
      {left right : SourceState} ->
      targetProvenance
        (Recognition.mapState actionRecognition left)
      ≡
      targetProvenance
        (Recognition.mapState actionRecognition right)
      ->
      sourceProvenance left ≡ sourceProvenance right

open ProvenancePreservingActionRecognition public

record ProvenancePreservingOrbitRecognition
    {SourceState SourceSymmetry TargetState TargetSymmetry : Set}
    {SourceProvenance TargetProvenance : Set}
    {sourceAction :
      Action.InvertibleSymmetryAction SourceState SourceSymmetry}
    {targetAction :
      Action.InvertibleSymmetryAction TargetState TargetSymmetry}
    {sourceProvenance : SourceState -> SourceProvenance}
    {targetProvenance : TargetState -> TargetProvenance}
    (provenanceRecognition :
      ProvenancePreservingActionRecognition
        sourceAction targetAction
        sourceProvenance targetProvenance)
    (sourceOrbits : Orbit.OrbitPresentation sourceAction)
    (targetOrbits : Orbit.OrbitPresentation targetAction) : Set₁ where
  constructor provenance-preserving-orbit-recognition
  field
    orbitRecognition :
      Recognition.OrbitRecognition
        (actionRecognition provenanceRecognition)
        sourceOrbits
        targetOrbits

    pi0Embedding :
      Recognition.Pi0Embedding orbitRecognition

    pi0Surjection :
      Recognition.Pi0Surjection orbitRecognition

    stabilizerRecognition :
      Recognition.StabilizerRecognition orbitRecognition

open ProvenancePreservingOrbitRecognition public

data SharedObservationCreatesSharedProvenance : Set where
data OrbitEqualityCreatesSharedProvenance : Set where
data EquivarianceCreatesAuthorityTransfer : Set where

sharedObservationDoesNotCreateSharedProvenance :
  SharedObservationCreatesSharedProvenance -> ⊥
sharedObservationDoesNotCreateSharedProvenance ()

orbitEqualityDoesNotCreateSharedProvenance :
  OrbitEqualityCreatesSharedProvenance -> ⊥
orbitEqualityDoesNotCreateSharedProvenance ()

equivarianceDoesNotCreateAuthorityTransfer :
  EquivarianceCreatesAuthorityTransfer -> ⊥
equivarianceDoesNotCreateAuthorityTransfer ()

record ProvenancePreservingRecognitionBoundary : Set where
  constructor provenance-preserving-recognition-boundary
  field
    actionEquivarianceStillRequired : Bool
    orbitRecognitionStillRequired : Bool
    provenanceCommutationRequired : Bool
    provenanceReflectionRequired : Bool
    sharedObservationFusesProvenance : Bool
    orbitEqualityFusesProvenance : Bool
    equivarianceTransfersAuthority : Bool

canonicalProvenancePreservingRecognitionBoundary :
  ProvenancePreservingRecognitionBoundary
canonicalProvenancePreservingRecognitionBoundary =
  provenance-preserving-recognition-boundary
    true true true true false false false
