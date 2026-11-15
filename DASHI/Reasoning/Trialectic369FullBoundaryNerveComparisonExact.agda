module DASHI.Reasoning.Trialectic369FullBoundaryNerveComparisonExact where

------------------------------------------------------------------------
-- FULL 6/12/8 BOUNDARY-NERVE COMPARISON MAX-CUT
--
-- The selected augmented relational corner-star has eight strata only because
-- it contains a star-global object above three selected faces, three selected
-- edges and one selected corner.  The literal Base369 cube boundary has no
-- global stratum: it consists only of 6 faces, 12 edges and 8 corners.
--
-- Consequently there is no rank-preserving two-sided equivalence between the
-- augmented eight-stratum relational index and the full boundary nerve.  The
-- obstruction is stronger than a cardinality observation: the relational
-- global object would have to map to a full-boundary stratum of global rank,
-- but no such stratum exists.
--
-- The maximal comparison retained here is the proper selected corner star:
-- three selected faces + three selected edges + one selected corner, realized
-- literally inside the existing 6/12/8 boundary nerve.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369Ternary27BoundaryNerveExact as Nerve
import DASHI.Foundations.Base369Ternary27CornerEightExact as Corners
import DASHI.Reasoning.Trialectic369CechAugmentedCornerStarIndexExact as Index
import DASHI.Reasoning.TrialecticDyadicCoverNerveExact as Dyadic

------------------------------------------------------------------------
-- 1. Literal full-boundary carrier.
------------------------------------------------------------------------

data BoundaryRank : Set where
  globalRank faceRank edgeRank cornerRank : BoundaryRank

data FullBoundaryStratum : Set where
  fullFace : Geometry.Face6 → FullBoundaryStratum
  fullEdge : Nerve.Edge12 → FullBoundaryStratum
  fullCorner : Corners.Corner3 → FullBoundaryStratum

fullBoundaryRank : FullBoundaryStratum → BoundaryRank
fullBoundaryRank (fullFace face) = faceRank
fullBoundaryRank (fullEdge edge) = edgeRank
fullBoundaryRank (fullCorner corner) = cornerRank

augmentedRelationalRank :
  Index.AugmentedRelationalStratum8 → BoundaryRank
augmentedRelationalRank Index.relationalGlobal = globalRank
augmentedRelationalRank Index.relationalAB = faceRank
augmentedRelationalRank Index.relationalBC = faceRank
augmentedRelationalRank Index.relationalCA = faceRank
augmentedRelationalRank Index.relationalOverlapA = edgeRank
augmentedRelationalRank Index.relationalOverlapB = edgeRank
augmentedRelationalRank Index.relationalOverlapC = edgeRank
augmentedRelationalRank Index.relationalTripleABC = cornerRank

fullFaceCountIsSix : Nerve.faceCount ≡ 6
fullFaceCountIsSix = refl

fullEdgeCountIsTwelve : Nerve.edgeCount ≡ 12
fullEdgeCountIsTwelve = refl

fullCornerCountIsEight : Nerve.cornerCount ≡ 8
fullCornerCountIsEight = refl

------------------------------------------------------------------------
-- 2. Exact rank obstruction to a full same-object equivalence.
------------------------------------------------------------------------

record RankPreservingFullBoundaryEquivalence : Set where
  constructor rank-preserving-full-boundary-equivalence
  field
    forward : Index.AugmentedRelationalStratum8 → FullBoundaryStratum
    backward : FullBoundaryStratum → Index.AugmentedRelationalStratum8
    forwardBackward :
      (full : FullBoundaryStratum) → forward (backward full) ≡ full
    backwardForward :
      (relational : Index.AugmentedRelationalStratum8) →
      backward (forward relational) ≡ relational
    rankForward :
      (relational : Index.AugmentedRelationalStratum8) →
      fullBoundaryRank (forward relational)
      ≡ augmentedRelationalRank relational

open RankPreservingFullBoundaryEquivalence public

globalRankAbsentFromFullBoundary :
  (full : FullBoundaryStratum) →
  fullBoundaryRank full ≡ globalRank → ⊥
globalRankAbsentFromFullBoundary (fullFace face) ()
globalRankAbsentFromFullBoundary (fullEdge edge) ()
globalRankAbsentFromFullBoundary (fullCorner corner) ()

rankPreservingFullBoundaryEquivalenceImpossible :
  RankPreservingFullBoundaryEquivalence → ⊥
rankPreservingFullBoundaryEquivalenceImpossible equivalence =
  globalRankAbsentFromFullBoundary
    (forward equivalence Index.relationalGlobal)
    (rankForward equivalence Index.relationalGlobal)

------------------------------------------------------------------------
-- 3. Maximal proper selected-corner-star comparison.
------------------------------------------------------------------------

data ProperSelectedRelationalStratum7 : Set where
  properAB properBC properCA : ProperSelectedRelationalStratum7
  properOverlapA properOverlapB properOverlapC : ProperSelectedRelationalStratum7
  properTripleABC : ProperSelectedRelationalStratum7

properToAugmented :
  ProperSelectedRelationalStratum7 →
  Index.AugmentedRelationalStratum8
properToAugmented properAB = Index.relationalAB
properToAugmented properBC = Index.relationalBC
properToAugmented properCA = Index.relationalCA
properToAugmented properOverlapA = Index.relationalOverlapA
properToAugmented properOverlapB = Index.relationalOverlapB
properToAugmented properOverlapC = Index.relationalOverlapC
properToAugmented properTripleABC = Index.relationalTripleABC

properToFullBoundary :
  ProperSelectedRelationalStratum7 → FullBoundaryStratum
properToFullBoundary properAB = fullFace Index.faceABGeometry
properToFullBoundary properBC = fullFace Index.faceBCGeometry
properToFullBoundary properCA = fullFace Index.faceCAGeometry
properToFullBoundary properOverlapA = fullEdge Index.edgeAGeometry
properToFullBoundary properOverlapB = fullEdge Index.edgeBGeometry
properToFullBoundary properOverlapC = fullEdge Index.edgeCGeometry
properToFullBoundary properTripleABC = fullCorner Index.tripleCornerGeometry

properSelectedRank : ProperSelectedRelationalStratum7 → BoundaryRank
properSelectedRank properAB = faceRank
properSelectedRank properBC = faceRank
properSelectedRank properCA = faceRank
properSelectedRank properOverlapA = edgeRank
properSelectedRank properOverlapB = edgeRank
properSelectedRank properOverlapC = edgeRank
properSelectedRank properTripleABC = cornerRank

properSelectedRealizationPreservesRank :
  (stratum : ProperSelectedRelationalStratum7) →
  fullBoundaryRank (properToFullBoundary stratum)
  ≡ properSelectedRank stratum
properSelectedRealizationPreservesRank properAB = refl
properSelectedRealizationPreservesRank properBC = refl
properSelectedRealizationPreservesRank properCA = refl
properSelectedRealizationPreservesRank properOverlapA = refl
properSelectedRealizationPreservesRank properOverlapB = refl
properSelectedRealizationPreservesRank properOverlapC = refl
properSelectedRealizationPreservesRank properTripleABC = refl

------------------------------------------------------------------------
-- 4. Triple-overlap firewall.
------------------------------------------------------------------------

literalDyadicTripleIntersectionStillEmpty :
  Dyadic.TripleIntersectionWitness → ⊥
literalDyadicTripleIntersectionStillEmpty =
  Dyadic.relationalDyadicTripleIntersectionEmpty

data AugmentedTripleWasAlreadyLiteralDyadicIntersection : Set where

augmentedTripleDoesNotRetroactivelyFillDyadicIntersection :
  AugmentedTripleWasAlreadyLiteralDyadicIntersection → ⊥
augmentedTripleDoesNotRetroactivelyFillDyadicIntersection ()

------------------------------------------------------------------------
-- 5. Result ledger.
------------------------------------------------------------------------

data ComparisonOutcome : Set where
  obstructedByMissingGlobalRank : ComparisonOutcome

comparisonOutcome : ComparisonOutcome
comparisonOutcome = obstructedByMissingGlobalRank

record Trialectic369FullBoundaryNerveComparisonBoundary : Set where
  constructor trialectic-369-full-boundary-nerve-comparison-boundary
  field
    fullBoundaryCountsOwned : Bool
    globalRankObstructionPaid : Bool
    rankPreservingFullEquivalencePaid : Bool
    selectedProperStarComparisonPaid : Bool
    literalDyadicTripleIntersectionInhabited : Bool
    augmentedTripleAddedSeparately : Bool
    selectedCornerStarEqualsWholeBoundaryNerve : Bool
    monsterRepresentationPromoted : Bool

open Trialectic369FullBoundaryNerveComparisonBoundary public

canonicalTrialectic369FullBoundaryNerveComparisonBoundary :
  Trialectic369FullBoundaryNerveComparisonBoundary
canonicalTrialectic369FullBoundaryNerveComparisonBoundary =
  trialectic-369-full-boundary-nerve-comparison-boundary
    true
    true
    false
    true
    false
    true
    false
    false
