module DASHI.Moonshine.OggSSPP2FrobeniusVsRetainedTargetNoGoExact where

------------------------------------------------------------------------
-- p=2 MOVING FROBENIUS VS IDENTITY-ONLY RETAINED TARGET
--
-- DASHI CONTRIBUTION
--
-- The current retained Base369 target has ten states and identity-only
-- morphisms.  Full recognition includes stabilizer reflection.  Therefore any
-- source symmetry mapped into the unit target symmetry must stabilize every
-- recognized source-orbit representative.
--
-- Consequence: a genuine p=2 Frobenius source with an orbit representative
-- moved by Frobenius cannot fully recognize the identity-only retained target.
--
-- This is stronger than the earlier 3-vs-10 component count obstruction.
-- It does NOT identify the correct arithmetic target; it only proves that
-- preserving a genuinely moving Frobenius requires a richer target action
-- presentation than the current discrete retained groupoid.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)

import DASHI.Core.ResidualSymmetryCollisionFibreExact as Action
import DASHI.Core.OrbitStabilizerResidualPresentationExact as Orbit
import DASHI.Core.ActionOrbitRecognitionFunctorExact as Recognition
import DASHI.Foundations.BalancedTernaryOrbitStabilizerResidualBridgeExact as C2
import DASHI.Moonshine.Base369P2FiveOrbitOrientationGroupoidsExact as Target
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Generic moving-C2 source.
------------------------------------------------------------------------

record MovingP2FrobeniusSource : Set₁ where
  field
    State : Set

    action :
      Action.InvertibleSymmetryAction State C2.C2

    orbits :
      Orbit.OrbitPresentation action

    movedOrbit :
      Orbit.Orbit orbits

    frobeniusMovesRepresentative :
      Action.act action C2.flip
        (Orbit.representative orbits movedOrbit)
      ≡
      Orbit.representative orbits movedOrbit
      ->
      ⊥

open MovingP2FrobeniusSource public

------------------------------------------------------------------------
-- 2. Any action functor into the unit-symmetry retained target maps flip to tt.
------------------------------------------------------------------------

mappedFlipIsUnit :
  (source : MovingP2FrobeniusSource) ->
  (functor :
    Recognition.ActionRecognitionFunctor
      (action source)
      Target.p2RetainedAction) ->
  Recognition.mapSymmetry functor C2.flip ≡ tt
mappedFlipIsUnit source functor = refl

targetUnitFixesEveryRepresentative :
  (orbit : Orbit.Orbit Target.p2RetainedOrbitPresentation) ->
  Action.act Target.p2RetainedAction tt
    (Orbit.representative Target.p2RetainedOrbitPresentation orbit)
  ≡
  Orbit.representative Target.p2RetainedOrbitPresentation orbit
targetUnitFixesEveryRepresentative orbit = refl

------------------------------------------------------------------------
-- 3. Full recognition contradiction.
------------------------------------------------------------------------

movingFrobeniusCannotFullyRecognizeIdentityRetainedTarget :
  (source : MovingP2FrobeniusSource) ->
  (functor :
    Recognition.ActionRecognitionFunctor
      (action source)
      Target.p2RetainedAction) ->
  Recognition.OrbitStabilizerRecognition
    functor
    (orbits source)
    Target.p2RetainedOrbitPresentation
  ->
  ⊥
movingFrobeniusCannotFullyRecognizeIdentityRetainedTarget
    source functor full =
  frobeniusMovesRepresentative source reflected
  where
    recognition :
      Recognition.OrbitRecognition
        functor
        (orbits source)
        Target.p2RetainedOrbitPresentation
    recognition = Recognition.orbitRecognition full

    stabilizers :
      Recognition.StabilizerRecognition recognition
    stabilizers = Recognition.stabilizerRecognition full

    reflected :
      Action.act (action source) C2.flip
        (Orbit.representative (orbits source) (movedOrbit source))
      ≡
      Orbit.representative (orbits source) (movedOrbit source)
    reflected =
      Recognition.reflectsMappedStabilizer
        stabilizers
        (movedOrbit source)
        C2.flip
        refl

------------------------------------------------------------------------
-- 4. Strong same-presentation recognition is therefore also impossible.
------------------------------------------------------------------------

movingFrobeniusCannotBePresentationIsomorphicToIdentityRetainedTarget :
  (source : MovingP2FrobeniusSource) ->
  (functor :
    Recognition.ActionRecognitionFunctor
      (action source)
      Target.p2RetainedAction) ->
  Recognition.ActionGroupoidPresentationIsomorphism
    functor
    (orbits source)
    Target.p2RetainedOrbitPresentation
  ->
  ⊥
movingFrobeniusCannotBePresentationIsomorphicToIdentityRetainedTarget
    source functor iso =
  movingFrobeniusCannotFullyRecognizeIdentityRetainedTarget
    source
    functor
    (Recognition.orbitStabilizerRecognition iso)

------------------------------------------------------------------------
-- 5. Boundary.
------------------------------------------------------------------------

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryNewExtension

record P2FrobeniusVsRetainedTargetBoundary : Set where
  constructor p2-frobenius-vs-retained-target-boundary
  field
    retainedTargetHasIdentityOnlySymmetry : Bool
    fullRecognitionReflectsStabilizers : Bool
    movingFrobeniusSourceCanFullyRecognizeCurrentRetainedTarget : Bool
    strongerPresentationIsomorphismPossible : Bool
    richerFrobeniusCompatibleTargetActionRequired : Bool

canonicalP2FrobeniusVsRetainedTargetBoundary :
  P2FrobeniusVsRetainedTargetBoundary
canonicalP2FrobeniusVsRetainedTargetBoundary =
  p2-frobenius-vs-retained-target-boundary
    true true false false true
