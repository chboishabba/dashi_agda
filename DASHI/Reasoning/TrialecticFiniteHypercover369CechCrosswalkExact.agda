module DASHI.Reasoning.TrialecticFiniteHypercover369CechCrosswalkExact where

------------------------------------------------------------------------
-- FINITE HYPERCOVER / BASE369 CECH CROSSWALK
--
-- Two mature descent geometries coexist in-repo:
--
--   relational triadic site:
--     global + 3 edge charts + 3 vertex overlaps,
--     empty ordinary triple intersection, attached irreducible face;
--
--   Base369 ternary-cube boundary:
--     6 face charts + 12 pairwise edges + 8 literal corner triple overlaps.
--
-- The first now carries a finite 1-truncated hypersheaf receipt.  The second
-- already carries invertible edge transports and a corner cocycle.  This file
-- records the productive structural crosswalk while retaining the previously
-- proved rank obstruction: these are NOT silently the same nerve/site.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.TrialecticFiniteTriadicHypersheafExact as RelHyper
import DASHI.Moonshine.Base369Ternary27FaceHypercubeCechGluingBidiExact as CubeCech
import DASHI.Reasoning.Trialectic369FullBoundaryNerveComparisonExact as Compare

relationalBoundary : RelHyper.TrialecticFiniteTriadicHypersheafBoundary
relationalBoundary = RelHyper.canonicalTrialecticFiniteTriadicHypersheafBoundary

cubeBoundary : CubeCech.FaceHypercubeCechBoundary
cubeBoundary = CubeCech.canonicalFaceHypercubeCechBoundary

comparisonBoundary : Compare.Trialectic369FullBoundaryNerveComparisonBoundary
comparisonBoundary = Compare.canonicalTrialectic369FullBoundaryNerveComparisonBoundary

relationalFiniteHypersheafReceipt :
  RelHyper.certifiedFiniteOneTruncatedHypersheaf relationalBoundary ≡ true
relationalFiniteHypersheafReceipt = refl

cubeSixFaceReceipt :
  CubeCech.sixFaceObjectsOwned cubeBoundary ≡ true
cubeSixFaceReceipt = refl

cubeTwelveEdgeReceipt :
  CubeCech.twelvePairwiseEdgeOverlapsOwned cubeBoundary ≡ true
cubeTwelveEdgeReceipt = refl

cubeEightCornerReceipt :
  CubeCech.eightTripleCornerOverlapsOwned cubeBoundary ≡ true
cubeEightCornerReceipt = refl

cubeInvertibleTransportReceipt :
  CubeCech.invertibleEdgeTransportInterfaceDefined cubeBoundary ≡ true
cubeInvertibleTransportReceipt = refl

cubeCornerCocycleReceipt :
  CubeCech.cornerCocycleRequired cubeBoundary ≡ true
cubeCornerCocycleReceipt = refl

fullBoundaryRankObstructionReceipt :
  Compare.globalRankObstructionPaid comparisonBoundary ≡ true
fullBoundaryRankObstructionReceipt = refl

fullBoundaryEquivalenceNotPaid :
  Compare.rankPreservingFullEquivalencePaid comparisonBoundary ≡ false
fullBoundaryEquivalenceNotPaid = refl

record TrialecticFiniteHypercover369CechCrosswalkBoundary : Set where
  constructor trialectic-finite-hypercover369-cech-crosswalk-boundary
  field
    relationalFiniteOneTruncatedHypersheafPaid : Bool
    cubeBoundarySixFacesPaid : Bool
    cubeBoundaryTwelveEdgesPaid : Bool
    cubeBoundaryEightCornersPaid : Bool
    cubeInvertibleEdgeTransportPaid : Bool
    cubeCornerCocyclePaid : Bool
    bothCarryFiniteTwoSkeletonDescentData : Bool
    relationalAndCubeNervesIdentified : Bool
    fullBoundaryRankObstructionRetained : Bool
    cubeCechUsedAsIndependentGeometryDonor : Bool

open TrialecticFiniteHypercover369CechCrosswalkBoundary public

canonicalTrialecticFiniteHypercover369CechCrosswalkBoundary :
  TrialecticFiniteHypercover369CechCrosswalkBoundary
canonicalTrialecticFiniteHypercover369CechCrosswalkBoundary =
  trialectic-finite-hypercover369-cech-crosswalk-boundary
    true true true true true true true false true true
