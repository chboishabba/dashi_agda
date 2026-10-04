module DASHI.Physics.Closure.NSClayFacingBFinalAnalyticFrontier20261004Exact where

------------------------------------------------------------------------
-- CLAY-FACING B / FINAL ANALYTIC FRONTIER AFTER MAX-CUT
--
-- This owner is the canonical scheduler after the 2026-10-04 literal-row and
-- Q4+E recuts.
--
-- Paid source architecture:
--   * B1/B2/B3 live blocks -> exact literal deep-pair rows;
--   * B4 live critical-touching block -> exact literal critical-touching rows;
--   * four literal-row estimates -> SAME local-ED uniform family compiler;
--   * B_localED aggregation is algebraic, not an independent theorem;
--   * Q4+E literal derivative + same-curve FTC are compiled;
--   * endpoint increment is split into positive terminal + negative initial;
--   * the negative endpoint orientation already has an R463 Cauchy/energy
--     producer, while positive orientation is reduced by R461 to an amplitude
--     square producer;
--   * Q5 remains a valid fallback, not a prerequisite of Q4+E;
--   * continuum/BKM assembly is already machine-checked conditional plumbing.
--
-- Genuine remaining analytic leaves, in execution priority:
--
--   B4_row(theta<1)
--     > B1_row
--     > B2_row / B3_row
--     > Q4_integrated_Gram
--     > E_plus_terminal_flux/amplitude
--     > Q5_signed_quintic   (fallback)
--     > B-continuation inputs.
--
-- No status below promotes an unproved Navier--Stokes estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSClayFacingBPositiveMaxCut20261004Exact as Positive
import DASHI.Physics.Closure.NSClayFacingBLiteralRowAnalyticMaxCut20261004Exact as Rows
import DASHI.Physics.Closure.NSClayFacingBLocalEDCompilerMaxCut20261004Exact as LocalED
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingLiteralRowsMaxCutExact as B4Rows
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalTouchingRowOperatorMaxCutExact as B4Operator
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406Q4EAnalyticMaxCutExact as Q4E
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406EndpointSplitMaxCutExact as Endpoint
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406ProducerChoiceMaxCutExact as B7
import DASHI.Physics.Closure.NSPeriodicCutoffUniformContinuumBKMCompletion as Continuum

data FinalBAnalyticLeaf : Set where
  b4LiteralRowStrictMargin : FinalBAnalyticLeaf
  b1LiteralRowsLocalED : FinalBAnalyticLeaf
  b2LiteralRowsLocalED : FinalBAnalyticLeaf
  b3LiteralRowsLocalED : FinalBAnalyticLeaf
  q4IntegratedOffDiagonalGram : FinalBAnalyticLeaf
  ePositiveTerminalFluxAmplitude : FinalBAnalyticLeaf
  q5DirectSignedQuintic : FinalBAnalyticLeaf
  bContinuationInputs : FinalBAnalyticLeaf

finalBLeafClosed : FinalBAnalyticLeaf → Bool
finalBLeafClosed b4LiteralRowStrictMargin =
  B4Operator.b4LiteralRowStrictEstimateClosedHere
finalBLeafClosed b1LiteralRowsLocalED =
  Positive.b1LiteralShellPhysicalPaymentClosed
finalBLeafClosed b2LiteralRowsLocalED =
  Positive.b2SignedShellEstimateClosed
finalBLeafClosed b3LiteralRowsLocalED =
  Positive.b3SignedIntraShellL2Closed
finalBLeafClosed q4IntegratedOffDiagonalGram =
  Q4E.q4eIntegratedGramBoundClosed
finalBLeafClosed ePositiveTerminalFluxAmplitude =
  Endpoint.q4ePositiveTerminalFluxUniformBoundClosedHere
finalBLeafClosed q5DirectSignedQuintic =
  B7.b7DirectSignedQuinticRouteClosed
finalBLeafClosed bContinuationInputs =
  Continuum.periodicContinuumBKMCompletionInputsInhabited

currentHighestInformationLeaf : FinalBAnalyticLeaf
currentHighestInformationLeaf = b4LiteralRowStrictMargin

preferredB7FirstLeaf : FinalBAnalyticLeaf
preferredB7FirstLeaf = q4IntegratedOffDiagonalGram

preferredB7SecondLeaf : FinalBAnalyticLeaf
preferredB7SecondLeaf = ePositiveTerminalFluxAmplitude

q5FallbackLeaf : FinalBAnalyticLeaf
q5FallbackLeaf = q5DirectSignedQuintic

------------------------------------------------------------------------
-- Closed compilers / removed pseudo-leaves.
------------------------------------------------------------------------

literalRowAnalyticCompilerClosed : Bool
literalRowAnalyticCompilerClosed = Rows.bLiteralRowAnalyticCompilerClosed

b4LiteralRowCarrierClosed : Bool
b4LiteralRowCarrierClosed = B4Rows.b4CriticalTouchingRowsSameObjectClosed

b4LiteralRowOperatorCompilerClosed : Bool
b4LiteralRowOperatorCompilerClosed =
  B4Operator.b4LiteralRowOperatorCompilerClosed

localEDAllocationCompilerClosed : Bool
localEDAllocationCompilerClosed = LocalED.bLocalEDAllocationCompilerClosed

localEDIndependentLeaf : Bool
localEDIndependentLeaf = LocalED.bLocalEDIndependentAnalyticLeaf

q4eDerivativeAndFTCCompilerClosed : Bool
q4eDerivativeAndFTCCompilerClosed =
  Q4E.q4eOffDiagonalFluxFTCClosedGivenOrdinaryScalarFTC

q4eEndpointSplitCompilerClosed : Bool
q4eEndpointSplitCompilerClosed =
  Endpoint.q4eEndpointIncrementSplitCompilerClosed

q4eNegativeEndpointSideAvailable : Bool
q4eNegativeEndpointSideAvailable =
  Endpoint.q4eNegativeEndpointOrientationProducerExists

q4ePositiveEndpointReducedToAmplitudeSquare : Bool
q4ePositiveEndpointReducedToAmplitudeSquare =
  Endpoint.q4ePositiveEndpointReducedToAmplitudeSquare

q4eRepresentationTemporalPlumbingRemaining : Bool
q4eRepresentationTemporalPlumbingRemaining =
  Q4E.q4eRepresentationOrTemporalPlumbingRemaining

q5IsFallbackNotPrerequisite : Bool
q5IsFallbackNotPrerequisite = true

bContinuationCompilerMachineChecked : Bool
bContinuationCompilerMachineChecked = true

r823ShouldReopen : Bool
r823ShouldReopen = false

oldB7UniversalCovarianceEqualityShouldReopen : Bool
oldB7UniversalCovarianceEqualityShouldReopen = false

finalBAnalyticFrontierClosed : Bool
finalBAnalyticFrontierClosed = false

clayPromotion : Bool
clayPromotion = false

------------------------------------------------------------------------
-- Receipts for scheduler invariants.
------------------------------------------------------------------------

literalRowAnalyticCompilerClosedIsTrue :
  literalRowAnalyticCompilerClosed ≡ true
literalRowAnalyticCompilerClosedIsTrue = refl

b4LiteralRowCarrierClosedIsTrue : b4LiteralRowCarrierClosed ≡ true
b4LiteralRowCarrierClosedIsTrue = refl

b4LiteralRowOperatorCompilerClosedIsTrue :
  b4LiteralRowOperatorCompilerClosed ≡ true
b4LiteralRowOperatorCompilerClosedIsTrue = refl

localEDAllocationCompilerClosedIsTrue :
  localEDAllocationCompilerClosed ≡ true
localEDAllocationCompilerClosedIsTrue = refl

localEDIndependentLeafIsFalse : localEDIndependentLeaf ≡ false
localEDIndependentLeafIsFalse = refl

q4eEndpointSplitCompilerClosedIsTrue :
  q4eEndpointSplitCompilerClosed ≡ true
q4eEndpointSplitCompilerClosedIsTrue = refl

q4eNegativeEndpointSideAvailableIsTrue :
  q4eNegativeEndpointSideAvailable ≡ true
q4eNegativeEndpointSideAvailableIsTrue = refl

q4eRepresentationTemporalPlumbingRemainingIsFalse :
  q4eRepresentationTemporalPlumbingRemaining ≡ false
q4eRepresentationTemporalPlumbingRemainingIsFalse = refl

q5IsFallbackNotPrerequisiteIsTrue : q5IsFallbackNotPrerequisite ≡ true
q5IsFallbackNotPrerequisiteIsTrue = refl

r823ShouldReopenIsFalse : r823ShouldReopen ≡ false
r823ShouldReopenIsFalse = refl

finalBAnalyticFrontierClosedIsFalse :
  finalBAnalyticFrontierClosed ≡ false
finalBAnalyticFrontierClosedIsFalse = refl
