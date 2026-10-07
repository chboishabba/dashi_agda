module DASHI.Physics.Closure.NSClayFacingBPureAnalysisFrontier20261005Exact where

------------------------------------------------------------------------
-- CLAY-FACING B / PURE-ANALYSIS FRONTIER AFTER PR #1039 MERGE
--
-- The representation/provenance programme is frozen.  This owner records only
-- theorem-producing analytic routes.
--
-- B4 has now advanced one more exact step.  The literal critical-touching row
-- fold is partitioned on the SAME row carrier into
--
--   principal = literal Core-Core rows,
--   defect    = literal Core-noncore rows,
--
-- with the exact live identity
--
--   criticalTouchingSigned = principal + defect.
--
-- Therefore the remaining B4 theorem is no longer to discover a decomposition.
-- It is exactly the pair of physical estimates
--
--   principal <= thetaP Mcore + cP ED
--   defect    <= thetaD Mcore + cD ED
--   thetaP + thetaD < 1,
--
-- uniformly in physical state/output/cutoff.  The generic strict-split
-- compiler then closes the literal B4 payment.  The older fixed quarter route
-- remains an optional producer only.
--
-- Preferred B7/Q4 route remains pointwise Gram -> dissipation, because ordinary
-- monotone/scaled integration is already compiled.  E+ remains one uniform
-- global amplitude-sum bound because finite output aggregation is cardinality
-- free.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSClayFacingBFinalAnalyticFrontier20261004Exact as Previous
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingPrincipalDefectRows20261007Exact as LiteralSplit
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalTouchingStrictSplitMaxCutExact as Split
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalTouchingQuarterMarginMaxCutExact as Quarter
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406Q4PointwiseSpacetimeMaxCutExact as Q4Pointwise
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406PositiveEndpointAmplitudeMaxCutExact as EndpointAmplitude

data PureBAnalyticLeaf : Set where
  b4PrincipalDefectPhysicalEstimates : PureBAnalyticLeaf
  b1LiteralRowsED : PureBAnalyticLeaf
  b2LiteralRowsED : PureBAnalyticLeaf
  b3LiteralRowsED : PureBAnalyticLeaf
  q4PointwisePhysicalGram : PureBAnalyticLeaf
  ePositiveGlobalAmplitudeSum : PureBAnalyticLeaf
  q5SignedQuinticFallback : PureBAnalyticLeaf
  bContinuationInputs : PureBAnalyticLeaf

pureBLeafClosed : PureBAnalyticLeaf → Bool
pureBLeafClosed b4PrincipalDefectPhysicalEstimates = false
pureBLeafClosed b1LiteralRowsED =
  Previous.finalBLeafClosed Previous.b1LiteralRowsLocalED
pureBLeafClosed b2LiteralRowsED =
  Previous.finalBLeafClosed Previous.b2LiteralRowsLocalED
pureBLeafClosed b3LiteralRowsED =
  Previous.finalBLeafClosed Previous.b3LiteralRowsLocalED
pureBLeafClosed q4PointwisePhysicalGram =
  Q4Pointwise.q4PointwisePhysicalGramEstimateClosedHere
pureBLeafClosed ePositiveGlobalAmplitudeSum =
  EndpointAmplitude.eGlobalAmplitudeSumProducerClosedHere
pureBLeafClosed q5SignedQuinticFallback =
  Previous.finalBLeafClosed Previous.q5DirectSignedQuintic
pureBLeafClosed bContinuationInputs =
  Previous.finalBLeafClosed Previous.bContinuationInputs

currentHighestInformationLeaf : PureBAnalyticLeaf
currentHighestInformationLeaf = b4PrincipalDefectPhysicalEstimates

------------------------------------------------------------------------
-- B4 exact progress and compiler surface.
------------------------------------------------------------------------

b4LiteralPrincipalDefectSplitClosed : Bool
b4LiteralPrincipalDefectSplitClosed =
  LiteralSplit.b4LiteralPrincipalDefectSplitClosed

b4PrincipalDefectPhysicalEstimatesClosed : Bool
b4PrincipalDefectPhysicalEstimatesClosed = false

b4DirectStrictMarginCompilerClosed : Bool
b4DirectStrictMarginCompilerClosed = Previous.b4LiteralRowOperatorCompilerClosed

b4GenericStrictSplitCompilerClosed : Bool
b4GenericStrictSplitCompilerClosed = Split.b4StrictSplitCompilerClosed

b4FixedQuarterMarginRequired : Bool
b4FixedQuarterMarginRequired = Split.b4StrictSplitRequiresQuarterMargin

b4QuarterMarginOptionalCompilerClosed : Bool
b4QuarterMarginOptionalCompilerClosed = Quarter.b4QuarterMarginCompilerClosed

b4ResearchLeafNowOnlyPhysicalEstimates : Bool
b4ResearchLeafNowOnlyPhysicalEstimates = true

------------------------------------------------------------------------
-- B7 compiler surface.
------------------------------------------------------------------------

q4PointwiseToSpacetimeCompilerClosed : Bool
q4PointwiseToSpacetimeCompilerClosed =
  Q4Pointwise.q4PointwiseToSpacetimeCompilerClosed

q4IntegratedBoundIndependentLeaf : Bool
q4IntegratedBoundIndependentLeaf =
  Q4Pointwise.q4IntegratedBoundIndependentResearchLeaf

ePositiveOutputAggregationClosed : Bool
ePositiveOutputAggregationClosed =
  EndpointAmplitude.ePositiveOutputAggregationClosed

ePositiveOutputAggregationAddsCardinalityFactor : Bool
ePositiveOutputAggregationAddsCardinalityFactor =
  EndpointAmplitude.ePositiveOutputAggregationIntroducesCardinalityFactor

bLocalEDIndependentLeaf : Bool
bLocalEDIndependentLeaf = Previous.localEDIndependentLeaf

q5IsFallbackNotPrerequisite : Bool
q5IsFallbackNotPrerequisite = Previous.q5IsFallbackNotPrerequisite

r823ShouldReopen : Bool
r823ShouldReopen = Previous.r823ShouldReopen

pureAnalysisFrontierClosed : Bool
pureAnalysisFrontierClosed = false

clayPromotion : Bool
clayPromotion = false

------------------------------------------------------------------------
-- Receipts.
------------------------------------------------------------------------

b4LiteralPrincipalDefectSplitClosedIsTrue :
  b4LiteralPrincipalDefectSplitClosed ≡ true
b4LiteralPrincipalDefectSplitClosedIsTrue = refl

b4PrincipalDefectPhysicalEstimatesClosedIsFalse :
  b4PrincipalDefectPhysicalEstimatesClosed ≡ false
b4PrincipalDefectPhysicalEstimatesClosedIsFalse = refl

b4GenericStrictSplitCompilerClosedIsTrue :
  b4GenericStrictSplitCompilerClosed ≡ true
b4GenericStrictSplitCompilerClosedIsTrue = refl

b4FixedQuarterMarginRequiredIsFalse :
  b4FixedQuarterMarginRequired ≡ false
b4FixedQuarterMarginRequiredIsFalse = refl

b4QuarterMarginOptionalCompilerClosedIsTrue :
  b4QuarterMarginOptionalCompilerClosed ≡ true
b4QuarterMarginOptionalCompilerClosedIsTrue = refl

b4ResearchLeafNowOnlyPhysicalEstimatesIsTrue :
  b4ResearchLeafNowOnlyPhysicalEstimates ≡ true
b4ResearchLeafNowOnlyPhysicalEstimatesIsTrue = refl

q4PointwiseToSpacetimeCompilerClosedIsTrue :
  q4PointwiseToSpacetimeCompilerClosed ≡ true
q4PointwiseToSpacetimeCompilerClosedIsTrue = refl

q4IntegratedBoundIndependentLeafIsFalse :
  q4IntegratedBoundIndependentLeaf ≡ false
q4IntegratedBoundIndependentLeafIsFalse = refl

ePositiveOutputAggregationClosedIsTrue :
  ePositiveOutputAggregationClosed ≡ true
ePositiveOutputAggregationClosedIsTrue = refl

ePositiveOutputAggregationAddsCardinalityFactorIsFalse :
  ePositiveOutputAggregationAddsCardinalityFactor ≡ false
ePositiveOutputAggregationAddsCardinalityFactorIsFalse = refl

bLocalEDIndependentLeafIsFalse : bLocalEDIndependentLeaf ≡ false
bLocalEDIndependentLeafIsFalse = refl

q5IsFallbackNotPrerequisiteIsTrue : q5IsFallbackNotPrerequisite ≡ true
q5IsFallbackNotPrerequisiteIsTrue = refl

r823ShouldReopenIsFalse : r823ShouldReopen ≡ false
r823ShouldReopenIsFalse = refl

pureAnalysisFrontierClosedIsFalse : pureAnalysisFrontierClosed ≡ false
pureAnalysisFrontierClosedIsFalse = refl
