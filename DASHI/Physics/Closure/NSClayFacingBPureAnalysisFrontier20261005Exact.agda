module DASHI.Physics.Closure.NSClayFacingBPureAnalysisFrontier20261005Exact where

------------------------------------------------------------------------
-- CLAY-FACING B / PURE-ANALYSIS FRONTIER AFTER PR #1039 MERGE
--
-- The representation/provenance programme is frozen.  This owner records only
-- theorem-producing analytic routes.
--
-- Highest-information B4 route:
--   literal critical row fold = principal + defect
--   principal <= thetaP Mcore + cP ED
--   defect    <= thetaD Mcore + cD ED
--   thetaP + thetaD < 1
--   ------------------------------------------------
--   critical  <= (thetaP+thetaD) Mcore + (cP+cD) ED.
--
-- This generic strict-split compiler is the canonical B4 research interface.
-- The older Gate-2A 1/6 + 1/12 = 1/4 route remains a lawful optional producer,
-- but it is not required and is not treated as same-object evidence.
--
-- Preferred B7/Q4 route is also sharpened: ordinary monotone/scaled
-- integration compiles a pointwise
--
--   G_offdiag,N(t) <= A * D_N(t)
--
-- plus cutoff-uniform integrated dissipation into the required integrated Gram
-- budget.  Thus time integration is not an independent Q4 research leaf.
--
-- For E+, R461 already reduces one fixed-output positive endpoint to an
-- amplitude square.  The new output aggregator proves
--
--   sum_k F_k^+ <= W * (sum_k a_k)^2
--
-- with no output-count factor.  Hence the endpoint research leaf is a single
-- cutoff-uniform global amplitude-sum bound on the literal companion family.
--
-- Remaining board:
--   B4 strict principal+defect attachment
--   B1 literal rows -> ED
--   B2 literal rows -> ED
--   B3 literal rows -> ED
--   Q4 pointwise physical off-diagonal Gram -> dissipation
--   E+ global physical amplitude-sum bound
--   Q5 direct signed quintic (fallback only)
--   B-continuation inputs.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSClayFacingBFinalAnalyticFrontier20261004Exact as Previous
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalTouchingStrictSplitMaxCutExact as Split
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalTouchingQuarterMarginMaxCutExact as Quarter
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406Q4PointwiseSpacetimeMaxCutExact as Q4Pointwise
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406PositiveEndpointAmplitudeMaxCutExact as EndpointAmplitude

data PureBAnalyticLeaf : Set where
  b4StrictSplitPhysicalAttachment : PureBAnalyticLeaf
  b1LiteralRowsED : PureBAnalyticLeaf
  b2LiteralRowsED : PureBAnalyticLeaf
  b3LiteralRowsED : PureBAnalyticLeaf
  q4PointwisePhysicalGram : PureBAnalyticLeaf
  ePositiveGlobalAmplitudeSum : PureBAnalyticLeaf
  q5SignedQuinticFallback : PureBAnalyticLeaf
  bContinuationInputs : PureBAnalyticLeaf

pureBLeafClosed : PureBAnalyticLeaf → Bool
pureBLeafClosed b4StrictSplitPhysicalAttachment =
  Split.b4StrictSplitPhysicalAttachmentClosedHere
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
currentHighestInformationLeaf = b4StrictSplitPhysicalAttachment

b4DirectStrictMarginCompilerClosed : Bool
b4DirectStrictMarginCompilerClosed = Previous.b4LiteralRowOperatorCompilerClosed

b4GenericStrictSplitCompilerClosed : Bool
b4GenericStrictSplitCompilerClosed = Split.b4StrictSplitCompilerClosed

b4FixedQuarterMarginRequired : Bool
b4FixedQuarterMarginRequired = Split.b4StrictSplitRequiresQuarterMargin

b4QuarterMarginOptionalCompilerClosed : Bool
b4QuarterMarginOptionalCompilerClosed = Quarter.b4QuarterMarginCompilerClosed

b4ResearchLeafNowStrictPrincipalPlusDefect : Bool
b4ResearchLeafNowStrictPrincipalPlusDefect = true

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

b4GenericStrictSplitCompilerClosedIsTrue :
  b4GenericStrictSplitCompilerClosed ≡ true
b4GenericStrictSplitCompilerClosedIsTrue = refl

b4FixedQuarterMarginRequiredIsFalse :
  b4FixedQuarterMarginRequired ≡ false
b4FixedQuarterMarginRequiredIsFalse = refl

b4QuarterMarginOptionalCompilerClosedIsTrue :
  b4QuarterMarginOptionalCompilerClosed ≡ true
b4QuarterMarginOptionalCompilerClosedIsTrue = refl

b4ResearchLeafNowStrictPrincipalPlusDefectIsTrue :
  b4ResearchLeafNowStrictPrincipalPlusDefect ≡ true
b4ResearchLeafNowStrictPrincipalPlusDefectIsTrue = refl

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
