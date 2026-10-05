module DASHI.Physics.Closure.NSClayFacingBPureAnalysisFrontier20261005Exact where

------------------------------------------------------------------------
-- CLAY-FACING B / PURE-ANALYSIS FRONTIER AFTER PR #1039 MERGE
--
-- The representation/provenance programme is frozen.  This owner records only
-- theorem-producing analytic routes.
--
-- Highest-information B4 route:
--   literal critical row fold = principal + defect
--   principal <= (1/6) Mcore + cP ED
--   defect    <= (1/12) Mcore + cD ED
--   ------------------------------------------------
--   critical  <= (1/4) Mcore + (cP+cD) ED, with 1/4 < 1.
--
-- The compiler for the last line is closed.  What remains is the physical
-- principal/defect attachment on the literal critical row carrier.
--
-- Remaining board after that:
--   B1 literal rows -> ED
--   B2 literal rows -> ED
--   B3 literal rows -> ED
--   Q4 integrated off-diagonal Gram
--   E+ uniform positive terminal flux/amplitude
--   Q5 direct signed quintic (fallback only)
--   B-continuation inputs.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSClayFacingBFinalAnalyticFrontier20261004Exact as Previous
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalTouchingQuarterMarginMaxCutExact as Quarter

data PureBAnalyticLeaf : Set where
  b4QuarterMarginPhysicalAttachment : PureBAnalyticLeaf
  b1LiteralRowsED : PureBAnalyticLeaf
  b2LiteralRowsED : PureBAnalyticLeaf
  b3LiteralRowsED : PureBAnalyticLeaf
  q4IntegratedGram : PureBAnalyticLeaf
  ePositiveTerminalFlux : PureBAnalyticLeaf
  q5SignedQuinticFallback : PureBAnalyticLeaf
  bContinuationInputs : PureBAnalyticLeaf

pureBLeafClosed : PureBAnalyticLeaf → Bool
pureBLeafClosed b4QuarterMarginPhysicalAttachment =
  Quarter.b4QuarterMarginPhysicalAttachmentClosedHere
pureBLeafClosed b1LiteralRowsED =
  Previous.finalBLeafClosed Previous.b1LiteralRowsLocalED
pureBLeafClosed b2LiteralRowsED =
  Previous.finalBLeafClosed Previous.b2LiteralRowsLocalED
pureBLeafClosed b3LiteralRowsED =
  Previous.finalBLeafClosed Previous.b3LiteralRowsLocalED
pureBLeafClosed q4IntegratedGram =
  Previous.finalBLeafClosed Previous.q4IntegratedOffDiagonalGram
pureBLeafClosed ePositiveTerminalFlux =
  Previous.finalBLeafClosed Previous.ePositiveTerminalFluxAmplitude
pureBLeafClosed q5SignedQuinticFallback =
  Previous.finalBLeafClosed Previous.q5DirectSignedQuintic
pureBLeafClosed bContinuationInputs =
  Previous.finalBLeafClosed Previous.bContinuationInputs

currentHighestInformationLeaf : PureBAnalyticLeaf
currentHighestInformationLeaf = b4QuarterMarginPhysicalAttachment

b4DirectStrictMarginCompilerClosed : Bool
b4DirectStrictMarginCompilerClosed = Previous.b4LiteralRowOperatorCompilerClosed

b4QuarterMarginCompilerClosed : Bool
b4QuarterMarginCompilerClosed = Quarter.b4QuarterMarginCompilerClosed

b4QuarterThetaStrictlyBelowOne : Bool
b4QuarterThetaStrictlyBelowOne = Quarter.b4QuarterThetaStrictlyBelowOne

b4ResearchLeafNowPrincipalPlusDefect : Bool
b4ResearchLeafNowPrincipalPlusDefect = true

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

b4QuarterMarginCompilerClosedIsTrue :
  b4QuarterMarginCompilerClosed ≡ true
b4QuarterMarginCompilerClosedIsTrue = refl

b4QuarterThetaStrictlyBelowOneIsTrue :
  b4QuarterThetaStrictlyBelowOne ≡ true
b4QuarterThetaStrictlyBelowOneIsTrue = refl

b4ResearchLeafNowPrincipalPlusDefectIsTrue :
  b4ResearchLeafNowPrincipalPlusDefect ≡ true
b4ResearchLeafNowPrincipalPlusDefectIsTrue = refl

bLocalEDIndependentLeafIsFalse : bLocalEDIndependentLeaf ≡ false
bLocalEDIndependentLeafIsFalse = refl

q5IsFallbackNotPrerequisiteIsTrue : q5IsFallbackNotPrerequisite ≡ true
q5IsFallbackNotPrerequisiteIsTrue = refl

r823ShouldReopenIsFalse : r823ShouldReopen ≡ false
r823ShouldReopenIsFalse = refl

pureAnalysisFrontierClosedIsFalse : pureAnalysisFrontierClosed ≡ false
pureAnalysisFrontierClosedIsFalse = refl
