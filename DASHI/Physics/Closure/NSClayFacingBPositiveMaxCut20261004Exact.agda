module DASHI.Physics.Closure.NSClayFacingBPositiveMaxCut20261004Exact where

------------------------------------------------------------------------
-- CLAY-FACING B / POSITIVE ROUTE MAX-CUT AFTER THE R823 DECISION SOURCE CHAIN
--
-- Exact representation work now completed in this pass:
--
--   * the three live deep-only R236 scalars are reconstructed as literal
--     unordered physical pair rows retaining their actual shell indices;
--   * B7 finite output aggregation is reduced through the existing R498 exact
--     remainder identity to one per-output direct-companion/covariance weld.
--
-- Therefore the surviving positive B leaves are no longer generic extraction
-- or global summation problems.  They are:
--
--   B1  rows -> literal infinity-shell Bernstein data + local ED allocation,
--   B2  signed DFL-DHH per-shell estimate on the extracted rows,
--   B3  signed DHH intra-shell L2 aggregation on the extracted rows,
--   B4  strict critical touching operator estimate with theta < 1,
--   B7  per-output direct-resolvent-companion = live covariance same-object,
--   Bcont continuum/periodic continuation inputs.
--
-- B4 remains the highest-information analytic wall.  B1-B3 are prerequisite
-- physical payments; B7 is now a local semantic weld rather than a global one.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionLiteralPairExtractionMaxCutExact as Extract
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalDeepFarLowLiteralInfinityShellPaymentExact as B1
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalDeepFarLowDeepHHFractionalShellPaymentExact as B2
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalDeepHHFractionalShellPaymentExact as B3
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalTouchingRelativeCovarianceExact as B4
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406DirectCompanionMaxCutExact as B7
import DASHI.Physics.Closure.NSPeriodicCutoffUniformContinuumBKMCompletion as Continuum

data PositiveBLeaf : Set where
  b1RowsToLiteralShellPayment : PositiveBLeaf
  b2ExtractedDFLDHHPerShellSignedEstimate : PositiveBLeaf
  b3ExtractedDHHIntraShellSignedL2 : PositiveBLeaf
  b4StrictCriticalSignedOperator : PositiveBLeaf
  b7PerOutputDirectCompanionCovarianceWeld : PositiveBLeaf
  bContinuationInputs : PositiveBLeaf

positiveBLeafClosed : PositiveBLeaf → Bool
positiveBLeafClosed b1RowsToLiteralShellPayment =
  B1.deepFarLowLiteralInfinityShellPhysicalExtractorInhabitedHere
positiveBLeafClosed b2ExtractedDFLDHHPerShellSignedEstimate =
  B2.deepFarLowDeepHHPerShellNullBernsteinEstimateInhabitedHere
positiveBLeafClosed b3ExtractedDHHIntraShellSignedL2 =
  B3.deepHHIntraShellSignedL2AggregationInhabitedHere
positiveBLeafClosed b4StrictCriticalSignedOperator =
  B4.criticalTouchingStrictOperatorCertificateInhabitedHere
positiveBLeafClosed b7PerOutputDirectCompanionCovarianceWeld =
  B7.b7PerOutputDirectCompanionCovarianceWeldClosed
positiveBLeafClosed bContinuationInputs =
  Continuum.periodicContinuumBKMCompletionInputsInhabited

------------------------------------------------------------------------
-- Newly paid exact infrastructure.
------------------------------------------------------------------------

deepPairExtractionClosed : Bool
deepPairExtractionClosed =
  Extract.b1LiteralDFLPairExtractionClosed

dflDhhPairExtractionClosed : Bool
dflDhhPairExtractionClosed =
  Extract.b2LiteralDFLDHHPairExtractionClosed

dhhPairExtractionClosed : Bool
dhhPairExtractionClosed =
  Extract.b3LiteralDHHPairExtractionClosed

pairRowsRetainActualShellIndices : Bool
pairRowsRetainActualShellIndices =
  Extract.literalRowsRetainActualShellIndices

r406GlobalAggregationClosed : Bool
r406GlobalAggregationClosed =
  B7.b7R406GlobalAggregationClosed

r406LiteralR498CarrierReused : Bool
r406LiteralR498CarrierReused =
  B7.b7R498LiteralRemainderCarrierReused

------------------------------------------------------------------------
-- Genuine remaining analytic / semantic leaves.
------------------------------------------------------------------------

b1LiteralShellPhysicalPaymentClosed : Bool
b1LiteralShellPhysicalPaymentClosed =
  B1.deepFarLowLiteralInfinityShellPhysicalExtractorInhabitedHere

b2SignedShellEstimateClosed : Bool
b2SignedShellEstimateClosed =
  B2.deepFarLowDeepHHPerShellNullBernsteinEstimateInhabitedHere

b3SignedIntraShellL2Closed : Bool
b3SignedIntraShellL2Closed =
  B3.deepHHIntraShellSignedL2AggregationInhabitedHere

b4StrictMarginClosed : Bool
b4StrictMarginClosed =
  B4.criticalTouchingStrictOperatorCertificateInhabitedHere

b7LocalSameObjectClosed : Bool
b7LocalSameObjectClosed =
  B7.b7PerOutputDirectCompanionCovarianceWeldClosed

continuationInputsClosed : Bool
continuationInputsClosed =
  Continuum.periodicContinuumBKMCompletionInputsInhabited

------------------------------------------------------------------------
-- Priority / trust boundary.
------------------------------------------------------------------------

data PositiveBPriority : Set where
  prerequisitePhysicalPayments : PositiveBPriority
  strictCriticalMargin : PositiveBPriority
  localR406SemanticWeld : PositiveBPriority
  continuation : PositiveBPriority

currentExecutionPriority : PositiveBPriority
currentExecutionPriority = prerequisitePhysicalPayments

highestInformationResearchWall : PositiveBPriority
highestInformationResearchWall = strictCriticalMargin

genericRepresentationWorkRemainingInB1B3 : Bool
genericRepresentationWorkRemainingInB1B3 = false

b4RequiresStrictThetaBelowOne : Bool
b4RequiresStrictThetaBelowOne = true

r823ReserveMachineryShouldReopen : Bool
r823ReserveMachineryShouldReopen = false

clayPromotion : Bool
clayPromotion = false

------------------------------------------------------------------------
-- Receipts.
------------------------------------------------------------------------

deepPairExtractionClosedIsTrue : deepPairExtractionClosed ≡ true
deepPairExtractionClosedIsTrue = refl

r406GlobalAggregationClosedIsTrue : r406GlobalAggregationClosed ≡ true
r406GlobalAggregationClosedIsTrue = refl

genericRepresentationWorkRemainingInB1B3IsFalse :
  genericRepresentationWorkRemainingInB1B3 ≡ false
genericRepresentationWorkRemainingInB1B3IsFalse = refl

b4RequiresStrictThetaBelowOneIsTrue : b4RequiresStrictThetaBelowOne ≡ true
b4RequiresStrictThetaBelowOneIsTrue = refl

r823ReserveMachineryShouldReopenIsFalse :
  r823ReserveMachineryShouldReopen ≡ false
r823ReserveMachineryShouldReopenIsFalse = refl
