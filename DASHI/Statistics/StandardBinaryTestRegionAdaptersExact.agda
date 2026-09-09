module DASHI.Statistics.StandardBinaryTestRegionAdaptersExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Statistics.BinaryTestDecisionDirectionalEvidenceExact as Binary
import DASHI.Statistics.HypothesisRegionGeometryExact as Region

------------------------------------------------------------------------
-- STANDARD BINARY-TEST REGION ADAPTER SHAPES
--
-- These are design shapes, not numerical implementations of p-values or
-- confidence intervals.  They record which scientific region a binary decision
-- rule is intended to interrogate and, crucially, which conclusions remain
-- unavailable without an additional result-to-region witness.
------------------------------------------------------------------------

data TestFamily : Set where
  oneSidedPositive : TestFamily
  oneSidedNegative : TestFamily
  twoSidedDifference : TestFamily
  equivalence : TestFamily
  nonInferiority : TestFamily

------------------------------------------------------------------------
-- Every family retains its binary action alphabet while declaring a possibly
-- ternary scientific geometry.  The centre is family-relative.
------------------------------------------------------------------------

record BinaryRegionTestDesign (Parameter Result : Set) : Set₁ where
  constructor binary-region-test-design
  field
    family : TestFamily
    geometry : Region.HypothesisRegionGeometry Parameter
    decision : Result → Binary.BinaryTestDecision

    RejectLicensedRegion : Result → Parameter → Set
    FailLicensedRegion : Result → Parameter → Set

    rejectReference : String
    failReference : String
    designReference : String

open BinaryRegionTestDesign public

------------------------------------------------------------------------
-- Family-specific boundary receipts.  These intentionally do not manufacture
-- region evidence.  They state which common verbal promotions are forbidden.
------------------------------------------------------------------------

data OneSidedFailMeansOppositeDirectionPermission : Set where

data TwoSidedFailMeansEqualityPermission : Set where

data EquivalenceFailMeansMeaningfulDifferencePermission : Set where

data NonInferiorityFailMeansInferiorityPermission : Set where

data RejectDifferenceMeansDirectionKnownPermission : Set where

oneSidedFailureDoesNotProveOppositeDirection :
  OneSidedFailMeansOppositeDirectionPermission → ⊥
oneSidedFailureDoesNotProveOppositeDirection ()

twoSidedFailureDoesNotProveEquality :
  TwoSidedFailMeansEqualityPermission → ⊥
twoSidedFailureDoesNotProveEquality ()

equivalenceFailureDoesNotProveMeaningfulDifference :
  EquivalenceFailMeansMeaningfulDifferencePermission → ⊥
equivalenceFailureDoesNotProveMeaningfulDifference ()

nonInferiorityFailureDoesNotProveInferiority :
  NonInferiorityFailMeansInferiorityPermission → ⊥
nonInferiorityFailureDoesNotProveInferiority ()

rejectingTwoSidedDifferenceDoesNotChooseDirection :
  RejectDifferenceMeansDirectionKnownPermission → ⊥
rejectingTwoSidedDifferenceDoesNotChooseDirection ()

------------------------------------------------------------------------
-- Interpretation matrix.  This is deliberately Boolean documentation of the
-- generic laws; concrete tests must still provide proof-bearing region receipts.
------------------------------------------------------------------------

record StandardBinaryRegionBoundary : Set where
  constructor standard-binary-region-boundary
  field
    oneSidedFailCanRemainUnderdetermined : Bool
    twoSidedFailProvesExactEquality : Bool
    equivalenceRequiresDedicatedRegionDesign : Bool
    nonInferiorityRequiresMarginRelativeRegion : Bool
    twoSidedRejectAloneDeterminesSign : Bool
    binaryActionAlphabetCanServeDifferentRegionGeometries : Bool

canonicalStandardBinaryRegionBoundary : StandardBinaryRegionBoundary
canonicalStandardBinaryRegionBoundary =
  standard-binary-region-boundary true false true true false true

------------------------------------------------------------------------
-- Residual-coordinate law.
--
-- A binary decision discards information relative to the richer scientific
-- region geometry unless a separate interpretation receipt carries it.  This is
-- the statistics-side analogue of embedding into a larger carrier while keeping
-- the added coordinate explicit; it is not an identification with any Base369
-- or codec semantics.
------------------------------------------------------------------------

record BinaryDecisionResidualCoordinate (Parameter Result : Set) : Set₁ where
  constructor binary-decision-residual-coordinate
  field
    design : BinaryRegionTestDesign Parameter Result
    Residual : Set
    residualOf : Result → Residual
    residualReference : String

open BinaryDecisionResidualCoordinate public

record BinaryDecisionResidualBoundary : Set where
  constructor binary-decision-residual-boundary
  field
    binaryDecisionExhaustsScientificInformation : Bool
    richerInterpretationMayRequireResidualCoordinate : Bool
    residualCoordinateMustRemainExplicit : Bool

canonicalBinaryDecisionResidualBoundary : BinaryDecisionResidualBoundary
canonicalBinaryDecisionResidualBoundary =
  binary-decision-residual-boundary false true true
