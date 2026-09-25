module DASHI.Reasoning.TrialecticEdgeSynthesisCompatibilityExact where

------------------------------------------------------------------------
-- THREE DIALECTICAL SYNTHESIS CELLS + IRREDUCIBLE TRIALECTIC FACE
--
-- DASHI CONTRIBUTION
--
-- A dialectical edge is not represented here as a bare opposition.  Reusing
-- TernaryComparisonSynthesisExact, every directed pair carries:
--
--   left position, right position, synthesis coordinate.
--
-- Thus an A-B-C trialectic may carry three first-order synthesis cells:
--
--   AB = (A , B , S_AB)
--   BC = (B , C , S_BC)
--   CA = (C , A , S_CA)
--
-- The shared participant coordinates must agree cyclically for these three
-- edge cells to form one compatible boundary family.
--
-- Crucially, even a compatible family of all three edge syntheses does not
-- determine the irreducible triadic face.  The face is an additional
-- coordinate.  Therefore:
--
--   three compatible dialectical syntheses
--     !=
--   forced trialectic synthesis.
--
-- A genuine "synthesis of syntheses" would require an additional face-level
-- gluing/mediation witness.  This module deliberately leaves that as an
-- explicit extra structure rather than manufacturing it from edge agreement.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import Base369 as Base
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Reasoning.TernaryComparisonSynthesisExact as Synthesis
import DASHI.Reasoning.TrialecticBoundaryFaceNonfactorabilityExact as Face
import DASHI.Reasoning.TrialecticProductiveJoinDescentExact as Productive

------------------------------------------------------------------------
-- 1. Endpoint observers on an existing synthesis choice.
------------------------------------------------------------------------

leftOf :
  Synthesis.SynthesisChoice27 →
  Base.TriTruth
leftOf (left , (right , synthesis)) = left

rightOf :
  Synthesis.SynthesisChoice27 →
  Base.TriTruth
rightOf (left , (right , synthesis)) = right

synthesisOf :
  Synthesis.SynthesisChoice27 →
  Base.TriTruth
synthesisOf = Synthesis.synthesisCoordinate

------------------------------------------------------------------------
-- 2. Three edge synthesis cells with cyclic endpoint compatibility.
------------------------------------------------------------------------

record CompatibleDialecticalTriangle : Set where
  constructor compatible-dialectical-triangle
  field
    edgeAB edgeBC edgeCA : Synthesis.SynthesisChoice27

    abRightMatchesBcLeft :
      rightOf edgeAB ≡ leftOf edgeBC

    bcRightMatchesCaLeft :
      rightOf edgeBC ≡ leftOf edgeCA

    caRightMatchesAbLeft :
      rightOf edgeCA ≡ leftOf edgeAB

open CompatibleDialecticalTriangle public

------------------------------------------------------------------------
-- Canonical finite fixture.
------------------------------------------------------------------------

canonicalAB : Synthesis.SynthesisChoice27
canonicalAB =
  Synthesis.makeSynthesisChoice
    Base.tri-low
    Base.tri-mid
    Base.tri-high

canonicalBC : Synthesis.SynthesisChoice27
canonicalBC =
  Synthesis.makeSynthesisChoice
    Base.tri-mid
    Base.tri-high
    Base.tri-low

canonicalCA : Synthesis.SynthesisChoice27
canonicalCA =
  Synthesis.makeSynthesisChoice
    Base.tri-high
    Base.tri-low
    Base.tri-mid

canonicalCompatibleDialecticalTriangle :
  CompatibleDialecticalTriangle
canonicalCompatibleDialecticalTriangle =
  compatible-dialectical-triangle
    canonicalAB
    canonicalBC
    canonicalCA
    refl
    refl
    refl

------------------------------------------------------------------------
-- 3. The three synthesis coordinates are retained independently.
------------------------------------------------------------------------

record EdgeSynthesisTriple : Set where
  constructor edge-synthesis-triple
  field
    synthesisAB synthesisBC synthesisCA : Base.TriTruth

open EdgeSynthesisTriple public

edgeSyntheses :
  CompatibleDialecticalTriangle →
  EdgeSynthesisTriple
edgeSyntheses triangle =
  edge-synthesis-triple
    (synthesisOf (edgeAB triangle))
    (synthesisOf (edgeBC triangle))
    (synthesisOf (edgeCA triangle))

canonicalEdgeSyntheses :
  edgeSyntheses canonicalCompatibleDialecticalTriangle
  ≡
  edge-synthesis-triple
    Base.tri-high
    Base.tri-low
    Base.tri-mid
canonicalEdgeSyntheses = refl

------------------------------------------------------------------------
-- 4. Attach an irreducible trialectic face above the compatible family.
------------------------------------------------------------------------

record TrialecticWithCompatibleEdgeSyntheses : Set where
  constructor trialectic-with-compatible-edge-syntheses
  field
    compatibleEdges : CompatibleDialecticalTriangle
    triadicFace : Face.TriadicFaceRelation

open TrialecticWithCompatibleEdgeSyntheses public

sameCompatibleEdgesReciprocal :
  TrialecticWithCompatibleEdgeSyntheses
sameCompatibleEdgesReciprocal =
  trialectic-with-compatible-edge-syntheses
    canonicalCompatibleDialecticalTriangle
    Face.reciprocalFace

sameCompatibleEdgesUnresolved :
  TrialecticWithCompatibleEdgeSyntheses
sameCompatibleEdgesUnresolved =
  trialectic-with-compatible-edge-syntheses
    canonicalCompatibleDialecticalTriangle
    Face.underdeterminedFace

sameCompatibleEdgesCoercive :
  TrialecticWithCompatibleEdgeSyntheses
sameCompatibleEdgesCoercive =
  trialectic-with-compatible-edge-syntheses
    canonicalCompatibleDialecticalTriangle
    Face.coerciveFace

compatibleEdgeObserver :
  TrialecticWithCompatibleEdgeSyntheses →
  CompatibleDialecticalTriangle
compatibleEdgeObserver = compatibleEdges

faceConsumer :
  TrialecticWithCompatibleEdgeSyntheses →
  Face.TriadicFaceRelation
faceConsumer = triadicFace

compatibleEdgesSameAcrossDifferentFaces :
  compatibleEdgeObserver sameCompatibleEdgesReciprocal
  ≡
  compatibleEdgeObserver sameCompatibleEdgesUnresolved
compatibleEdgesSameAcrossDifferentFaces = refl

faceStillDiffersAfterAllThreeEdgeSynthesesGlue :
  faceConsumer sameCompatibleEdgesReciprocal
  ≡
  faceConsumer sameCompatibleEdgesUnresolved
  →
  ⊥
faceStillDiffersAfterAllThreeEdgeSynthesesGlue ()

compatibleSynthesisFamilyDoesNotDetermineFace :
  Descent.FactorsThrough compatibleEdgeObserver faceConsumer →
  ⊥
compatibleSynthesisFamilyDoesNotDetermineFace =
  Descent.nonDescentWitnessBlocksFactorization
    (Descent.consumerNonDescentWitness
      sameCompatibleEdgesReciprocal
      sameCompatibleEdgesUnresolved
      compatibleEdgesSameAcrossDifferentFaces
      faceStillDiffersAfterAllThreeEdgeSynthesesGlue)

------------------------------------------------------------------------
-- 5. Optional second-order face gluing.
--
-- This is the extra structure required before one may talk about a
-- "synthesis of syntheses".  It is intentionally abstract: the repository
-- does not infer it merely because the three edge syntheses are compatible.
------------------------------------------------------------------------

record FaceLevelGluingWitness
    (state : TrialecticWithCompatibleEdgeSyntheses) : Set₁ where
  field
    FaceSynthesis : Set
    faceSynthesis : FaceSynthesis
    witnessesMediation :
      Face.TriadicFaceRelation →
      EdgeSynthesisTriple →
      FaceSynthesis →
      Set

    mediationReceipt :
      witnessesMediation
        (triadicFace state)
        (edgeSyntheses (compatibleEdges state))
        faceSynthesis

open FaceLevelGluingWitness public

data CompatibleEdgesForceFaceLevelGluing : Set where

compatibleEdgesDoNotForceFaceLevelGluing :
  CompatibleEdgesForceFaceLevelGluing →
  ⊥
compatibleEdgesDoNotForceFaceLevelGluing ()

------------------------------------------------------------------------
-- 6. Existing productive-join owner remains the first-order dialectical
-- gluing owner for historically richer fibres.
------------------------------------------------------------------------

existingThreeProductiveJoinsAreNotWholeTrialectic :
  Productive.ThreeProductiveJoinsAreWholeTrialectic →
  ⊥
existingThreeProductiveJoinsAreNotWholeTrialectic =
  Productive.threeProductiveJoinsDoNotBecomeWholeTrialectic

record TrialecticEdgeSynthesisCompatibilityBoundary : Set where
  constructor trialectic-edge-synthesis-compatibility-boundary
  field
    dialecticalEdgeRetainsSynthesisCoordinate : Bool
    threeEdgeSynthesesCanFormCompatibleCyclicBoundary : Bool
    compatibleThreeEdgeSynthesesDetermineTriadicFace : Bool
    triadicFaceIsAdditionalCoordinate : Bool
    faceLevelSynthesisAutomaticallyExists : Bool
    productiveJoinOwnerStillOwnsRicherFirstOrderGluing : Bool

canonicalTrialecticEdgeSynthesisCompatibilityBoundary :
  TrialecticEdgeSynthesisCompatibilityBoundary
canonicalTrialecticEdgeSynthesisCompatibilityBoundary =
  trialectic-edge-synthesis-compatibility-boundary
    true
    true
    false
    true
    false
    true
