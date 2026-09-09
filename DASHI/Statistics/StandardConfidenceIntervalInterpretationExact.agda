module DASHI.Statistics.StandardConfidenceIntervalInterpretationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Statistics.ConfidenceIntervalRegionEvidenceExact as CI
import DASHI.Statistics.HypothesisRegionGeometryExact as Region
import DASHI.Statistics.StandardBinaryTestRegionAdaptersExact as BinaryRegion

------------------------------------------------------------------------
-- STANDARD CONFIDENCE-INTERVAL INTERPRETATION SHAPES
--
-- This layer connects interval geometry to the standard families already owned
-- by StandardBinaryTestRegionAdaptersExact.  It deliberately does not assert a
-- confidence level, coverage theorem, asymptotic approximation, or test/CI
-- duality.  Those are separate statistical receipts.
------------------------------------------------------------------------

record ConfidenceIntervalTestInterpretation
    (Parameter : Set) : Set₁ where
  constructor confidence-interval-test-interpretation
  field
    order : CI.OrderedIntervalGeometry Parameter
    family : BinaryRegion.TestFamily
    geometry : Region.HypothesisRegionGeometry Parameter
    interval : CI.ConfidenceInterval order

    intervalEvidence : CI.IntervalRegionEvidence geometry interval

    confidenceProcedureReference : String
    coverageReference : String
    effectScaleReference : String
    marginReference : String

open ConfidenceIntervalTestInterpretation public

------------------------------------------------------------------------
-- Region receipts are intentionally family-relative.  For example, an interval
-- wholly inside an equivalence region supports an equivalence conclusion; an
-- interval merely failing to fit inside that region does not prove a meaningful
-- difference.  Similarly, containing a null value does not prove the null.
------------------------------------------------------------------------

data ContainsNullMeansNullTruePermission : Set where

data ExcludesNullMeansUniversalAlternativePermission : Set where

data FailedEquivalenceContainmentMeansDifferencePermission : Set where

data FailedNonInferiorityContainmentMeansInferiorityPermission : Set where

data TwoSidedExclusionChoosesDirectionPermission : Set where

containsNullDoesNotProveNullTrue :
  ContainsNullMeansNullTruePermission → ⊥
containsNullDoesNotProveNullTrue ()

excludesNullDoesNotProveEveryAlternative :
  ExcludesNullMeansUniversalAlternativePermission → ⊥
excludesNullDoesNotProveEveryAlternative ()

failedEquivalenceContainmentDoesNotProveDifference :
  FailedEquivalenceContainmentMeansDifferencePermission → ⊥
failedEquivalenceContainmentDoesNotProveDifference ()

failedNonInferiorityContainmentDoesNotProveInferiority :
  FailedNonInferiorityContainmentMeansInferiorityPermission → ⊥
failedNonInferiorityContainmentDoesNotProveInferiority ()

twoSidedExclusionDoesNotByItselfChooseDirection :
  TwoSidedExclusionChoosesDirectionPermission → ⊥
twoSidedExclusionDoesNotByItselfChooseDirection ()

------------------------------------------------------------------------
-- Test/interval duality is not assumed generically.  If a concrete statistical
-- procedure wants to identify a binary test decision with a CI containment
-- statement, it must supply the equivalence as a proof-bearing receipt.
------------------------------------------------------------------------

record TestIntervalDualityReceipt
    {Parameter Result : Set}
    (test : BinaryRegion.BinaryRegionTestDesign Parameter Result)
    (order : CI.OrderedIntervalGeometry Parameter)
    (intervalOf : Result → CI.ConfidenceInterval order) : Set₁ where
  constructor test-interval-duality-receipt
  field
    RejectCharacterisation : Result → Set
    FailCharacterisation : Result → Set

    rejectSound :
      ∀ {result} →
      RejectCharacterisation result →
      BinaryRegion.decision test result
      ≡ DASHI.Statistics.BinaryTestDecisionDirectionalEvidenceExact.rejectNull

    failSound :
      ∀ {result} →
      FailCharacterisation result →
      BinaryRegion.decision test result
      ≡ DASHI.Statistics.BinaryTestDecisionDirectionalEvidenceExact.failToRejectNull

    dualityReference : String

open TestIntervalDualityReceipt public

record StandardConfidenceIntervalBoundary : Set where
  constructor standard-confidence-interval-boundary
  field
    confidenceIntervalIsBinaryDecision : Bool
    containsNullProvesNullTrue : Bool
    failedEquivalenceProvesDifference : Bool
    failedNonInferiorityProvesInferiority : Bool
    twoSidedNullExclusionAloneChoosesDirection : Bool
    testIntervalDualityRequiresReceipt : Bool
    intervalGeometryCanCarryResidualDirectionInformation : Bool

canonicalStandardConfidenceIntervalBoundary : StandardConfidenceIntervalBoundary
canonicalStandardConfidenceIntervalBoundary =
  standard-confidence-interval-boundary
    false false false false false true true
