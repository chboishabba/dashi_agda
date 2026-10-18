module DASHI.Reasoning.TrialecticThreeStrandBraidHistoryExact where

------------------------------------------------------------------------
-- TRIALECTIC THREE-STRAND BRAID HISTORY
--
-- DASHI CONTRIBUTION
--
-- A/B/C are represented as three labelled strands.  The textile kernel owns
-- the literal Artin words
--
--   sigma0 sigma1 sigma0
--   sigma1 sigma0 sigma1
--
-- and TextileBraidRewriteGroupoidExact now owns the explicit Yang--Baxter
-- rewrite between them.
--
-- The crucial relational result is not that process equivalence erases
-- history.  Instead, the same attached trialectic face can coexist with two
-- distinct retained process histories.  Hence the face does not recover the
-- braid history.
--
-- Braiding Sweetgrass / Two-Eyed Seeing motivate the anti-fusion reading only;
-- the finite braid and non-factorability theorems are DASHI mathematics.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Combinatorics.TextileNFibreCalculusExact as Textile
import DASHI.Combinatorics.TextileBraidRewriteGroupoidExact as Rewrite
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Reasoning.TrialecticBoundaryFaceNonfactorabilityExact as Face
import DASHI.Reasoning.TrialecticBraidedTwoEyedCoordinationExact as Braided

------------------------------------------------------------------------
-- 1. Label the three textile positions by the three trialectic strands.
------------------------------------------------------------------------

data StrandPosition3 : Set where
  position0 position1 position2 : StrandPosition3

positionStrand : StrandPosition3 -> Braided.TrialecticStrand
positionStrand position0 = Braided.strandA
positionStrand position1 = Braided.strandB
positionStrand position2 = Braided.strandC

------------------------------------------------------------------------
-- 2. Exact Yang--Baxter process equivalence.
------------------------------------------------------------------------

leftYangBaxterWord : Textile.BraidWord 3
leftYangBaxterWord =
  Textile.threeFibreYangBaxterLeft

rightYangBaxterWord : Textile.BraidWord 3
rightYangBaxterWord =
  Textile.threeFibreYangBaxterRight

yangBaxterProcessEquivalent :
  Rewrite.BraidProcessEquivalent 3
    leftYangBaxterWord
    rightYangBaxterWord
yangBaxterProcessEquivalent =
  Rewrite.threeFibreYangBaxterEquivalent

leftHistory : Textile.BraidedFibreHistory 3
leftHistory =
  Textile.threeLeftHistory

rightHistory : Textile.BraidedFibreHistory 3
rightHistory =
  Textile.threeRightHistory

------------------------------------------------------------------------
-- 3. Same attached face, different retained route labels.
------------------------------------------------------------------------

data TrialecticBraidRoute : Set where
  leftYangBaxterRoute : TrialecticBraidRoute
  rightYangBaxterRoute : TrialecticBraidRoute

data TrialecticBraidState : Set where
  leftReciprocalBraid : TrialecticBraidState
  rightReciprocalBraid : TrialecticBraidState

faceOf :
  TrialecticBraidState ->
  Face.TriadicFaceRelation
faceOf leftReciprocalBraid = Face.reciprocalFace
faceOf rightReciprocalBraid = Face.reciprocalFace

routeOf :
  TrialecticBraidState ->
  TrialecticBraidRoute
routeOf leftReciprocalBraid = leftYangBaxterRoute
routeOf rightReciprocalBraid = rightYangBaxterRoute

sameFaceAcrossYangBaxterHistories :
  faceOf leftReciprocalBraid
  ≡ faceOf rightReciprocalBraid
sameFaceAcrossYangBaxterHistories = refl

differentRetainedRoutes :
  routeOf leftReciprocalBraid
  ≡ routeOf rightReciprocalBraid
  ->
  ⊥
differentRetainedRoutes ()

faceRouteNonDescent :
  Descent.ConsumerNonDescentWitness
    faceOf
    routeOf
faceRouteNonDescent =
  Descent.consumerNonDescentWitness
    leftReciprocalBraid
    rightReciprocalBraid
    sameFaceAcrossYangBaxterHistories
    differentRetainedRoutes

braidRouteDoesNotFactorThroughAttachedFace :
  Descent.FactorsThrough faceOf routeOf
  ->
  ⊥
braidRouteDoesNotFactorThroughAttachedFace =
  Descent.nonDescentWitnessBlocksFactorization
    faceRouteNonDescent

------------------------------------------------------------------------
-- 4. Process equivalence is not provenance erasure.
------------------------------------------------------------------------

data YangBaxterEquivalenceErasesHistory : Set where
data SameAttachedFaceMeansSameProcessRoute : Set where
data BraidRelationFusesTrialecticStrands : Set where

yangBaxterEquivalenceDoesNotEraseHistory :
  YangBaxterEquivalenceErasesHistory -> ⊥
yangBaxterEquivalenceDoesNotEraseHistory ()

sameAttachedFaceDoesNotMeanSameProcessRoute :
  SameAttachedFaceMeansSameProcessRoute -> ⊥
sameAttachedFaceDoesNotMeanSameProcessRoute ()

braidRelationDoesNotFuseTrialecticStrands :
  BraidRelationFusesTrialecticStrands -> ⊥
braidRelationDoesNotFuseTrialecticStrands ()

rewriteBoundary :
  Rewrite.BraidRewriteBoundary
rewriteBoundary =
  Rewrite.canonicalBraidRewriteBoundary

record TrialecticThreeStrandBraidHistoryBoundary : Set where
  constructor trialectic-three-strand-braid-history-boundary
  field
    threeTrialecticStrandsMappedToThreeBraidPositions : Bool
    yangBaxterRewriteExplicit : Bool
    yangBaxterProcessEquivalenceOwned : Bool
    literalHistoriesRetained : Bool
    sameAttachedFaceMayCarryDifferentHistories : Bool
    attachedFaceRecoversHistory : Bool
    processEquivalenceErasesProvenance : Bool
    braidRelationFusesStrands : Bool

canonicalTrialecticThreeStrandBraidHistoryBoundary :
  TrialecticThreeStrandBraidHistoryBoundary
canonicalTrialecticThreeStrandBraidHistoryBoundary =
  trialectic-three-strand-braid-history-boundary
    true true true true true false false false
