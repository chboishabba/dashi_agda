module DASHI.Reasoning.TrialecticBoundaryFaceNonfactorabilityExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- A trialectic is not definitionally three simultaneous dialectics.
-- The three dyadic edge dispositions form a boundary.  An irreducible
-- triadic face relation is retained as a further coordinate.  Two states can
-- have the same three edges and different face relations; therefore the face
-- consumer does not factor through the boundary projection.
--
-- Peircean triadic mediation is a source-level motivation only.  The finite
-- collision theorem below is a DASHI construction and is not attributed to
-- Peirce or to any psychological source.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.RelationalTrialecticSourceAtlasExact as Sources

data EdgeDisposition : Set where
  negativeEdge : EdgeDisposition
  neutralEdge : EdgeDisposition
  positiveEdge : EdgeDisposition

record TrialecticBoundary : Set where
  constructor trialectic-boundary
  field
    edgeAB : EdgeDisposition
    edgeBC : EdgeDisposition
    edgeCA : EdgeDisposition

open TrialecticBoundary public

boundaryStateCount : Nat
boundaryStateCount = 3 * 3 * 3

boundaryStateCountIs27 : boundaryStateCount ≡ 27
boundaryStateCountIs27 = refl

data TriadicFaceRelation : Set where
  reciprocalFace : TriadicFaceRelation
  coerciveFace : TriadicFaceRelation
  underdeterminedFace : TriadicFaceRelation

record TrialecticState : Set where
  constructor trialectic-state
  field
    boundary : TrialecticBoundary
    face : TriadicFaceRelation

open TrialecticState public

boundaryObserver : TrialecticState → TrialecticBoundary
boundaryObserver = boundary

faceConsumer : TrialecticState → TriadicFaceRelation
faceConsumer = face

sharedPositiveBoundary : TrialecticBoundary
sharedPositiveBoundary =
  trialectic-boundary positiveEdge positiveEdge positiveEdge

sameEdgesReciprocal : TrialecticState
sameEdgesReciprocal =
  trialectic-state sharedPositiveBoundary reciprocalFace

sameEdgesCoercive : TrialecticState
sameEdgesCoercive =
  trialectic-state sharedPositiveBoundary coerciveFace

sameThreeEdges :
  boundaryObserver sameEdgesReciprocal
  ≡ boundaryObserver sameEdgesCoercive
sameThreeEdges = refl

differentTriadicFace :
  faceConsumer sameEdgesReciprocal
  ≡ faceConsumer sameEdgesCoercive →
  ⊥
differentTriadicFace ()

boundaryFaceNonDescent :
  Descent.ConsumerNonDescentWitness boundaryObserver faceConsumer
boundaryFaceNonDescent =
  Descent.consumerNonDescentWitness
    sameEdgesReciprocal
    sameEdgesCoercive
    sameThreeEdges
    differentTriadicFace

triadicFaceCannotFactorThroughThreeEdges :
  Descent.FactorsThrough boundaryObserver faceConsumer → ⊥
triadicFaceCannotFactorThroughThreeEdges =
  Descent.nonDescentWitnessBlocksFactorization boundaryFaceNonDescent

data ThreeDyadsDetermineTrialectic : Set where

threeDyadsDoNotDetermineTrialectic :
  ThreeDyadsDetermineTrialectic → ⊥
threeDyadsDoNotDetermineTrialectic ()

record TrialecticBoundaryFaceBoundary : Set where
  constructor trialectic-boundary-face-boundary
  field
    boundaryCarrierHas27States : Bool
    faceRetainedBeyondBoundary : Bool
    threeDyadsDetermineFace : Bool
    boundaryProjectionRecoversWholeTrialectic : Bool
    sourceCitationProvesNonfactorability : Bool

canonicalTrialecticBoundaryFaceBoundary :
  TrialecticBoundaryFaceBoundary
canonicalTrialecticBoundaryFaceBoundary =
  trialectic-boundary-face-boundary true true false false false
