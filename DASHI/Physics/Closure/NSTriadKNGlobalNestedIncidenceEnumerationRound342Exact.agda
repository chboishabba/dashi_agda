module DASHI.Physics.Closure.NSTriadKNGlobalNestedIncidenceEnumerationRound342Exact where

------------------------------------------------------------------------
-- ROUND342 / BIDI CORRECTION: GLOBAL NESTED PAIR LIST IS ALSO OLD-CARRIER
--
-- R341 correctly identifies the pair *type* required by NSPairIncidenceKernel:
--
--   Pair = R330.NestedIncidence
--        = PhysicalTriadIncidence × PhysicalTriadIncidence.
--
-- But PairIncidenceData.pairs is one global finite list, whereas
-- R330.literalNestedRow cutoff k is deliberately a row-dependent fixed-output
-- list.  Those are not the same object and must not be identified merely
-- because their element type agrees.
--
-- Repository archaeology removes the need for a new global enumerator anyway.
-- `NSTriadKNPhysicalTriadEnumeration` already owns the complete finite list of
-- physical outer triads in the cutoff cube.  R330 already owns the operation
-- which, for every outer triad, enumerates the complete inner output fibre at
-- its forcing leg p.  Therefore the global nested-pair list is simply their
-- composition.
--
-- This round closes only that carrier/list seam.  It does NOT manufacture:
--
--   * row/column coordinates for the Schur operator,
--   * the heat-weighted pairContribution,
--   * a pointwise concrete-kernel match,
--   * a row/column budget,
--   * or Package A.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNLiteralNestedRowEnumerationRound330Exact as R330

-- Exact global finite pair list for the old PairIncidenceData.pairs field.
-- No new pair datatype and no new finite enumeration algorithm are introduced.
globalNestedIncidences : Nat → List R330.NestedIncidence
globalNestedIncidences cutoff =
  R330.nestedRowsFromOuters cutoff
    (Physical.physicalTriadEnumeration cutoff)

globalNestedIncidencesIsOldComposition :
  ∀ cutoff →
  globalNestedIncidences cutoff ≡
    R330.nestedRowsFromOuters cutoff
      (Physical.physicalTriadEnumeration cutoff)
globalNestedIncidencesIsOldComposition cutoff = refl

round342PairTypeAlreadyOwned : Bool
round342PairTypeAlreadyOwned = true

round342GlobalOuterEnumerationAlreadyOwned : Bool
round342GlobalOuterEnumerationAlreadyOwned = true

round342InnerFiberExpansionAlreadyOwned : Bool
round342InnerFiberExpansionAlreadyOwned = true

round342GlobalNestedPairListClosedByComposition : Bool
round342GlobalNestedPairListClosedByComposition = true

-- Important correction to R341: a fixed-output row is not definitionally the
-- global PairIncidenceData.pairs list.
round342FixedOutputRowIsGlobalPairList : Bool
round342FixedOutputRowIsGlobalPairList = false

round342RowCoordinateSemanticsClosed : Bool
round342RowCoordinateSemanticsClosed = false

round342ColumnCoordinateSemanticsClosed : Bool
round342ColumnCoordinateSemanticsClosed = false

round342HeatWeightedPairContributionClosed : Bool
round342HeatWeightedPairContributionClosed = false

round342ConcreteKernelPointwiseMatchClosed : Bool
round342ConcreteKernelPointwiseMatchClosed = false

round342WeightedSchurCertificateClosed : Bool
round342WeightedSchurCertificateClosed = false

round342PackageAClosed : Bool
round342PackageAClosed = false

round342ClayPromotion : Bool
round342ClayPromotion = false

round342GlobalNestedPairListClosedByCompositionIsTrue :
  round342GlobalNestedPairListClosedByComposition ≡ true
round342GlobalNestedPairListClosedByCompositionIsTrue = refl

round342FixedOutputRowIsGlobalPairListIsFalse :
  round342FixedOutputRowIsGlobalPairList ≡ false
round342FixedOutputRowIsGlobalPairListIsFalse = refl

round342PackageAClosedIsFalse : round342PackageAClosed ≡ false
round342PackageAClosedIsFalse = refl

round342ClayPromotionIsFalse : round342ClayPromotion ≡ false
round342ClayPromotionIsFalse = refl
