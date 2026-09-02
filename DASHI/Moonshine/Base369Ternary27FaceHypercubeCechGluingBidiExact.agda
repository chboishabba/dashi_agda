module DASHI.Moonshine.Base369Ternary27FaceHypercubeCechGluingBidiExact where

------------------------------------------------------------------------
-- EQUIVARIANT CECH-STYLE GLUING FOR THE SIX FACE-ATTACHED X6 HYPERCUBES
--
-- The boundary nerve supplies:
--   6 face objects,
--   12 pairwise edge overlaps,
--   8 corner triple overlaps.
--
-- Edge transports are oriented by the nerve constructors:
--   xy : x-face -> y-face
--   yz : y-face -> z-face
--   xz : x-face -> z-face.
--
-- At every corner the cocycle law is therefore
--
--   T_xz = T_yz o T_xy.
--
-- This file separates a model-side gluing law from the stronger promotion in
-- which all face charts land in one literal actual state/action.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369Ternary27CornerEightExact as Corners
import DASHI.Foundations.Base369Ternary27BoundaryNerveExact as Nerve
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H

------------------------------------------------------------------------
-- 1. Model-side equivariant gluing data.
------------------------------------------------------------------------

record FaceHypercubeCechGluing (Actor : Set) : Set₁ where
  field
    faceAct : Geometry.Face6 → Actor → H.X6 → H.X6

    edgeTransport : (edge : Nerve.Edge12) → H.X6 → H.X6
    edgeTransportInverse : (edge : Nerve.Edge12) → H.X6 → H.X6

    edgeInverseAfterForward :
      (edge : Nerve.Edge12) →
      (state : H.X6) →
      edgeTransportInverse edge (edgeTransport edge state) ≡ state

    edgeForwardAfterInverse :
      (edge : Nerve.Edge12) →
      (state : H.X6) →
      edgeTransport edge (edgeTransportInverse edge state) ≡ state

    edgeTransportIntertwines :
      (edge : Nerve.Edge12) →
      (actor : Actor) →
      (state : H.X6) →
      edgeTransport edge
        (faceAct (Nerve.edgeFirstFace edge) actor state)
      ≡
      faceAct (Nerve.edgeSecondFace edge) actor
        (edgeTransport edge state)

    edgeInverseIntertwines :
      (edge : Nerve.Edge12) →
      (actor : Actor) →
      (state : H.X6) →
      edgeTransportInverse edge
        (faceAct (Nerve.edgeSecondFace edge) actor state)
      ≡
      faceAct (Nerve.edgeFirstFace edge) actor
        (edgeTransportInverse edge state)

    cornerCocycle :
      (corner : Corners.Corner3) →
      (state : H.X6) →
      let edges = Nerve.cornerIncidentEdges corner
      in edgeTransport (Nerve.incidentXZEdge edges) state
       ≡ edgeTransport (Nerve.incidentYZEdge edges)
           (edgeTransport (Nerve.incidentXYEdge edges) state)
open FaceHypercubeCechGluing public

------------------------------------------------------------------------
-- 2. The gluing interface is nonempty at model level: one common X6 action
--    gives identity transition maps.  This is NOT Monster recognition.
------------------------------------------------------------------------

uniformModelGluing :
  {Actor : Set} →
  (act : Actor → H.X6 → H.X6) →
  FaceHypercubeCechGluing Actor
uniformModelGluing act = record
  { faceAct = λ face actor state → act actor state
  ; edgeTransport = λ edge state → state
  ; edgeTransportInverse = λ edge state → state
  ; edgeInverseAfterForward = λ edge state → refl
  ; edgeForwardAfterInverse = λ edge state → refl
  ; edgeTransportIntertwines = λ edge actor state → refl
  ; edgeInverseIntertwines = λ edge actor state → refl
  ; cornerCocycle = λ corner state → refl
  }

------------------------------------------------------------------------
-- 3. Actual same-object promotion.
--
-- Each face chart must inject into ONE literal ActualState.  On an edge, the
-- two face descriptions must become equal in that actual carrier after the
-- certified edge transition.  The same actual Actor action must intertwine
-- every face inclusion.
------------------------------------------------------------------------

record ActualFaceHypercubeGluingPromotion
  (Actor ActualState : Set) : Set₁ where
  field
    modelGluing : FaceHypercubeCechGluing Actor
    actualAct : Actor → ActualState → ActualState
    includeFace : Geometry.Face6 → H.X6 → ActualState

    includeFaceInjective :
      (face : Geometry.Face6) →
      {left right : H.X6} →
      includeFace face left ≡ includeFace face right →
      left ≡ right

    includeFaceIntertwines :
      (face : Geometry.Face6) →
      (actor : Actor) →
      (state : H.X6) →
      includeFace face
        (faceAct modelGluing face actor state)
      ≡ actualAct actor (includeFace face state)

    edgeDescriptionsAgreeInActualState :
      (edge : Nerve.Edge12) →
      (state : H.X6) →
      includeFace (Nerve.edgeSecondFace edge)
        (edgeTransport modelGluing edge state)
      ≡ includeFace (Nerve.edgeFirstFace edge) state
open ActualFaceHypercubeGluingPromotion public

------------------------------------------------------------------------
-- 4. Promotion consequences: at a corner, direct x->z transport and the
--    composite x->y->z transport already agree before entering ActualState.
------------------------------------------------------------------------

cornerTransportCoherence :
  {Actor : Set} →
  (gluing : FaceHypercubeCechGluing Actor) →
  (corner : Corners.Corner3) →
  (state : H.X6) →
  let edges = Nerve.cornerIncidentEdges corner
  in edgeTransport gluing (Nerve.incidentXZEdge edges) state
   ≡ edgeTransport gluing (Nerve.incidentYZEdge edges)
       (edgeTransport gluing (Nerve.incidentXYEdge edges) state)
cornerTransportCoherence gluing = cornerCocycle gluing

record FaceHypercubeCechBoundary : Set where
  constructor faceHypercubeCechBoundary
  field
    sixFaceObjectsOwned : Bool
    twelvePairwiseEdgeOverlapsOwned : Bool
    eightTripleCornerOverlapsOwned : Bool
    invertibleEdgeTransportInterfaceDefined : Bool
    actorEquivarianceRequiredOnEveryEdge : Bool
    cornerCocycleRequired : Bool
    identityModelGluingConstructed : Bool
    modelGluingImpliesActualMonsterGluing : Bool
    actualPromotionRequiresOneLiteralStateAndAction : Bool

canonicalFaceHypercubeCechBoundary : FaceHypercubeCechBoundary
canonicalFaceHypercubeCechBoundary =
  faceHypercubeCechBoundary true true true true true true true false true
