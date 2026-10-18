module DASHI.Foundations.TrialecticDepthHyperformExact where

------------------------------------------------------------------------
-- DEPTH-INDEXED WHOLE TRIALECTIC HYPERFORM
--
-- DASHI CONTRIBUTION
--
-- This binds the 3x3 observer surface, three-edge boundary, irreducible face,
-- and gluing status into one depth-indexed carrier.  Truncation may identify
-- fine states whose finer gluing status differs.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Reasoning.TrialecticObserverMatrix369Exact as Matrix
import DASHI.Reasoning.TrialecticBoundaryFaceNonfactorabilityExact as Face
import DASHI.Foundations.RelationalDepthPresheafExact as Depth

record TrialecticHyperformAt (depth : Nat) : Set where
  constructor trialectic-hyperform-at
  field
    observerMatrix : Matrix.ObserverMatrix3 Face.EdgeDisposition
    boundary : Face.TrialecticBoundary
    face : Face.TriadicFaceRelation
    gluingStatus : Depth.GluingStatus

open TrialecticHyperformAt public

record TrialecticDepthSystem : Set₁ where
  field
    truncate :
      (depth : Nat) →
      TrialecticHyperformAt (suc depth) →
      TrialecticHyperformAt depth

open TrialecticDepthSystem public

uniformMatrix : Matrix.ObserverMatrix3 Face.EdgeDisposition
uniformMatrix =
  Matrix.observerMatrix3
    Face.neutralEdge Face.neutralEdge Face.neutralEdge
    Face.neutralEdge Face.neutralEdge Face.neutralEdge
    Face.neutralEdge Face.neutralEdge Face.neutralEdge

uniformBoundary : Face.TrialecticBoundary
uniformBoundary =
  Face.trialectic-boundary
    Face.neutralEdge Face.neutralEdge Face.neutralEdge

coarseLayer : TrialecticHyperformAt zero
coarseLayer =
  trialectic-hyperform-at
    uniformMatrix uniformBoundary Face.underdeterminedFace Depth.glues

fineLayerLeft : TrialecticHyperformAt (suc zero)
fineLayerLeft =
  trialectic-hyperform-at
    uniformMatrix uniformBoundary Face.reciprocalFace Depth.glues

fineLayerRight : TrialecticHyperformAt (suc zero)
fineLayerRight =
  trialectic-hyperform-at
    uniformMatrix uniformBoundary Face.coerciveFace Depth.obstructed

truncateTrialectic :
  (depth : Nat) →
  TrialecticHyperformAt (suc depth) →
  TrialecticHyperformAt depth
truncateTrialectic zero state = coarseLayer
truncateTrialectic (suc depth) state =
  trialectic-hyperform-at
    (observerMatrix state)
    (boundary state)
    (face state)
    (gluingStatus state)

canonicalTrialecticDepthSystem : TrialecticDepthSystem
canonicalTrialecticDepthSystem =
  record { truncate = truncateTrialectic }

fineLayersCollideAtCoarseDepth :
  truncate canonicalTrialecticDepthSystem zero fineLayerLeft
  ≡ truncate canonicalTrialecticDepthSystem zero fineLayerRight
fineLayersCollideAtCoarseDepth = refl

fineGluingStatusesDiffer :
  gluingStatus fineLayerLeft ≡ gluingStatus fineLayerRight → ⊥
fineGluingStatusesDiffer ()

record TrialecticDepthHyperformBoundary : Set where
  constructor trialectic-depth-hyperform-boundary
  field
    relationalLocalityAndDepthAreDistinctAxes : Bool
    wholeTrialecticCarrierIsDepthIndexed : Bool
    coarseAgreementForcesFineGluing : Bool
    truncationMayEraseFineFaceAndGluingState : Bool
    depthIndexIsAutomaticallyEuclideanDistance : Bool

canonicalTrialecticDepthHyperformBoundary :
  TrialecticDepthHyperformBoundary
canonicalTrialecticDepthHyperformBoundary =
  trialectic-depth-hyperform-boundary true true false true false
