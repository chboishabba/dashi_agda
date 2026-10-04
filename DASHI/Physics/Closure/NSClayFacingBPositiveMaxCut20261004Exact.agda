module DASHI.Physics.Closure.NSClayFacingBPositiveMaxCut20261004Exact where

------------------------------------------------------------------------
-- CLAY-FACING B / POSITIVE ROUTE MAX-CUT AFTER THE R823 DECISION SOURCE CHAIN
--
-- Exact representation work now completed in this pass:
--
--   * the three live deep-only R236 scalars are reconstructed as literal
--     unordered physical pair rows retaining their actual shell indices;
--   * those exact rows compile into the existing B1/B2/B3 payment records, so
--     analytic producers no longer restate live-block same-object equalities;
--   * R498 closes B7 finite output aggregation on the literal R406 carrier;
--   * the attempted universal direct-companion = coherent-covariance equality
--     is rejected by the R289/R611 degree audit (5 versus 4);
--   * the exact R406 debt+flux-tangent and endpoint normal forms are already
--     available with no new NS estimate.
--
-- Surviving positive B leaves:
--
--   B1  extracted rows -> literal shell/Bernstein payment + local ED allocation,
--   B2  signed DFL-DHH per-shell estimate on the extracted rows,
--   B3  signed DHH intra-shell L2 aggregation on the extracted rows,
--   B4  strict critical touching operator estimate with theta < 1,
--   B7  ONE valid R406 producer route:
--         (Q5) direct signed quintic spacetime budget, OR
--         (Q4+E) quartic Gram + weighted-flux endpoint bounds,
--   Bcont continuum/periodic continuation inputs.
--
-- B4 remains the highest-information strict analytic wall.  B7 is a genuine
-- analytic producer choice, not a representation weld and not two cumulative
-- obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionLiteralPairExtractionMaxCutExact as Extract
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalDeepBlocksFromLiteralRowsMaxCutExact as RowCompiler
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalDeepFarLowLiteralInfinityShellPaymentExact as B1
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalDeepFarLowDeepHHFractionalShellPaymentExact as B2
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalDeepHHFractionalShellPaymentExact as B3
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalTouchingRelativeCovarianceExact as B4
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406DirectCompanionMaxCutExact as B7Direct
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406HomogeneityBoundaryMaxCutExact as B7Boundary
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406DynamicMaxCutExact as B7Dynamic
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406ProducerChoiceMaxCutExact as B7Producer
import DASHI.Physics.Closure.NSPeriodicCutoffUniformContinuumBKMCompletion as Continuum

boolOr : Bool → Bool → Bool
boolOr true _ = true
boolOr false b = b

data PositiveBLeaf : Set where
  b1RowsToLiteralShellPayment : PositiveBLeaf
  b2ExtractedDFLDHHPerShellSignedEstimate : PositiveBLeaf
  b3ExtractedDHHIntraShellSignedL2 : PositiveBLeaf
  b4StrictCriticalSignedOperator : PositiveBLeaf
  b7OneValidR406Producer : PositiveBLeaf
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
positiveBLeafClosed b7OneValidR406Producer =
  boolOr B7Producer.b7DirectSignedQuinticRouteClosed
    B7Producer.b7QuarticGramEndpointRouteClosed
positiveBLeafClosed bContinuationInputs =
  Continuum.periodicContinuumBKMCompletionInputsInhabited

------------------------------------------------------------------------
-- Newly paid exact infrastructure.
------------------------------------------------------------------------

deepPairExtractionClosed : Bool
deepPairExtractionClosed = Extract.b1LiteralDFLPairExtractionClosed

dflDhhPairExtractionClosed : Bool
dflDhhPairExtractionClosed = Extract.b2LiteralDFLDHHPairExtractionClosed

dhhPairExtractionClosed : Bool
dhhPairExtractionClosed = Extract.b3LiteralDHHPairExtractionClosed

pairRowsRetainActualShellIndices : Bool
pairRowsRetainActualShellIndices = Extract.literalRowsRetainActualShellIndices

b1B3LiveBlockSameObjectFieldsCompiledFromRows : Bool
b1B3LiveBlockSameObjectFieldsCompiledFromRows =
  RowCompiler.b1B3LiveBlockSameObjectFieldsCompiledFromRows

r406GlobalAggregationClosed : Bool
r406GlobalAggregationClosed = B7Direct.b7R406GlobalAggregationClosed

r406LiteralR498CarrierReused : Bool
r406LiteralR498CarrierReused = B7Direct.b7R498LiteralRemainderCarrierReused

b7UniversalSameObjectEqualityAdmissible : Bool
b7UniversalSameObjectEqualityAdmissible =
  B7Boundary.b7UniversalDirectCompanionCovarianceEqualityAdmissible

b7DebtPlusFluxTangentDecompositionClosed : Bool
b7DebtPlusFluxTangentDecompositionClosed =
  B7Dynamic.b7R406DebtPlusFluxTangentDecompositionClosed

b7ExactEndpointNormalFormCompilerClosed : Bool
b7ExactEndpointNormalFormCompilerClosed =
  B7Producer.b7ExactEndpointNormalFormCompilerClosed

b7QuarticGramEndpointCompilerAvailable : Bool
b7QuarticGramEndpointCompilerAvailable =
  B7Producer.b7QuarticGramEndpointCompilerAvailable

------------------------------------------------------------------------
-- Genuine remaining analytic / producer leaves.
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

b7DirectSignedQuinticRouteClosed : Bool
b7DirectSignedQuinticRouteClosed =
  B7Producer.b7DirectSignedQuinticRouteClosed

b7QuarticGramEndpointRouteClosed : Bool
b7QuarticGramEndpointRouteClosed =
  B7Producer.b7QuarticGramEndpointRouteClosed

b7OneProducerRouteClosed : Bool
b7OneProducerRouteClosed =
  boolOr b7DirectSignedQuinticRouteClosed b7QuarticGramEndpointRouteClosed

continuationInputsClosed : Bool
continuationInputsClosed =
  Continuum.periodicContinuumBKMCompletionInputsInhabited

------------------------------------------------------------------------
-- Priority / trust boundary.
------------------------------------------------------------------------

data PositiveBPriority : Set where
  prerequisitePhysicalPayments : PositiveBPriority
  strictCriticalMargin : PositiveBPriority
  r406Producer : PositiveBPriority
  continuation : PositiveBPriority

currentExecutionPriority : PositiveBPriority
currentExecutionPriority = prerequisitePhysicalPayments

highestInformationResearchWall : PositiveBPriority
highestInformationResearchWall = strictCriticalMargin

genericRepresentationWorkRemainingInB1B3 : Bool
genericRepresentationWorkRemainingInB1B3 = false

b4RequiresStrictThetaBelowOne : Bool
b4RequiresStrictThetaBelowOne = true

b7UniversalEqualityRouteRejectedByHomogeneity : Bool
b7UniversalEqualityRouteRejectedByHomogeneity = true

b7RepresentationOnlyWorkRemaining : Bool
b7RepresentationOnlyWorkRemaining = false

r823ReserveMachineryShouldReopen : Bool
r823ReserveMachineryShouldReopen = false

clayPromotion : Bool
clayPromotion = false

------------------------------------------------------------------------
-- Receipts.
------------------------------------------------------------------------

deepPairExtractionClosedIsTrue : deepPairExtractionClosed ≡ true
deepPairExtractionClosedIsTrue = refl

b1B3LiveBlockSameObjectFieldsCompiledFromRowsIsTrue :
  b1B3LiveBlockSameObjectFieldsCompiledFromRows ≡ true
b1B3LiveBlockSameObjectFieldsCompiledFromRowsIsTrue = refl

r406GlobalAggregationClosedIsTrue : r406GlobalAggregationClosed ≡ true
r406GlobalAggregationClosedIsTrue = refl

b7UniversalSameObjectEqualityAdmissibleIsFalse :
  b7UniversalSameObjectEqualityAdmissible ≡ false
b7UniversalSameObjectEqualityAdmissibleIsFalse = refl

b7DebtPlusFluxTangentDecompositionClosedIsTrue :
  b7DebtPlusFluxTangentDecompositionClosed ≡ true
b7DebtPlusFluxTangentDecompositionClosedIsTrue = refl

b7ExactEndpointNormalFormCompilerClosedIsTrue :
  b7ExactEndpointNormalFormCompilerClosed ≡ true
b7ExactEndpointNormalFormCompilerClosedIsTrue = refl

b7QuarticGramEndpointCompilerAvailableIsTrue :
  b7QuarticGramEndpointCompilerAvailable ≡ true
b7QuarticGramEndpointCompilerAvailableIsTrue = refl

genericRepresentationWorkRemainingInB1B3IsFalse :
  genericRepresentationWorkRemainingInB1B3 ≡ false
genericRepresentationWorkRemainingInB1B3IsFalse = refl

b4RequiresStrictThetaBelowOneIsTrue : b4RequiresStrictThetaBelowOne ≡ true
b4RequiresStrictThetaBelowOneIsTrue = refl

b7RepresentationOnlyWorkRemainingIsFalse :
  b7RepresentationOnlyWorkRemaining ≡ false
b7RepresentationOnlyWorkRemainingIsFalse = refl

r823ReserveMachineryShouldReopenIsFalse :
  r823ReserveMachineryShouldReopen ≡ false
r823ReserveMachineryShouldReopenIsFalse = refl
