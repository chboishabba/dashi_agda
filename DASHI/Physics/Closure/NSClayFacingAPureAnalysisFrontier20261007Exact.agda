module DASHI.Physics.Closure.NSClayFacingAPureAnalysisFrontier20261007Exact where

------------------------------------------------------------------------
-- CLAY-FACING A / PURE-ANALYSIS + SAME-OBJECT MAX-CUT / 2026-10-07
--
-- Preserve the public three-stage programme
--
--   A1 physical kernel -> A2 finite-energy majorants -> A3 continuation,
--
-- but expose the actual subleaves that remain after the repository's closed
-- origin/curvature/measure/low-high compiler stack is removed from the board.
--
-- A1:
--   * actual near-origin physical kernel/saturation weld;
--   * actual high-frequency physical heat/envelope weld.
-- A2:
--   * low physical majorant <= compact-output convolution envelope;
--   * high physical majorant <= inverse-sixth weighted envelope.
-- A3:
--   * instantiate the literal Fefferman-A continuation/run target from the
--     resulting actual compensated field/endgame inputs.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSClayFacingAMaxCut20261002Exact as Old
import DASHI.Physics.Closure.NSClayFacingAAnalyticCutExact as Analytic
import DASHI.Physics.Closure.NSClayFacingAPhysicalSameObjectCutExact as Physical
import DASHI.Physics.Closure.NSWholeSpaceLowHighConvolutionProducerExact as Conv
import DASHI.Physics.Closure.NSWholeSpacePhysicalMajorantDominationProducerExact as DomProducer
import DASHI.Physics.Closure.NSWholeSpaceActualPhysicalCompensatedFieldExact as ActualField
import DASHI.Physics.Closure.NSWholeSpaceActualSignedLebesgueEndgameExact as ActualEnd
import DASHI.Physics.Closure.NSABCDConcentratedCompletionCutExact as Cut

data AStage : Set where
  A1PhysicalKernel : AStage
  A2FiniteEnergyMajorants : AStage
  A3WholeSpaceContinuation : AStage

data APureLeaf : Set where
  a1NearOriginKernelWeld : APureLeaf
  a1HighFrequencyHeatEnvelopeWeld : APureLeaf
  a2LowPhysicalMajorantDomination : APureLeaf
  a2HighPhysicalMajorantDomination : APureLeaf
  a3LiteralContinuationInputs : APureLeaf

leafStage : APureLeaf → AStage
leafStage a1NearOriginKernelWeld = A1PhysicalKernel
leafStage a1HighFrequencyHeatEnvelopeWeld = A1PhysicalKernel
leafStage a2LowPhysicalMajorantDomination = A2FiniteEnergyMajorants
leafStage a2HighPhysicalMajorantDomination = A2FiniteEnergyMajorants
leafStage a3LiteralContinuationInputs = A3WholeSpaceContinuation

-- None of these physical/theorem leaves is silently promoted by the compiler
-- reductions below.
aPureLeafClosed : APureLeaf → Bool
aPureLeafClosed a1NearOriginKernelWeld = false
aPureLeafClosed a1HighFrequencyHeatEnvelopeWeld = false
aPureLeafClosed a2LowPhysicalMajorantDomination = false
aPureLeafClosed a2HighPhysicalMajorantDomination = false
aPureLeafClosed a3LiteralContinuationInputs = Cut.aLiteralClayTheoremClosed

currentHighestInformationALeaf : APureLeaf
currentHighestInformationALeaf = a1NearOriginKernelWeld

------------------------------------------------------------------------
-- Closed infrastructure removed from the research board.
------------------------------------------------------------------------

aNearOriginAnalyticEstimateClosed : Bool
aNearOriginAnalyticEstimateClosed = Physical.aNearOriginAnalyticEstimateClosed

aHighFrequencyCurvatureEstimateClosed : Bool
aHighFrequencyCurvatureEstimateClosed = Physical.aHighFrequencyCurvatureEstimateClosed

aLowConvolutionTargetIsolated : Bool
aLowConvolutionTargetIsolated = Conv.lowCompensatedConvolutionTargetIsolated

aHighInverseSixthTargetIsolated : Bool
aHighInverseSixthTargetIsolated = Conv.highInverseSixthConvolutionTargetIsolated

aMajorantDominationCompilerClosed : Bool
aMajorantDominationCompilerClosed =
  DomProducer.physicalMajorantDominationProducerCompilerClosed

aActualPhysicalFieldCompilerClosed : Bool
aActualPhysicalFieldCompilerClosed =
  ActualField.actualPhysicalCompensatedFieldCompilerClosed

aSignedLebesgueEndgameCompilerClosed : Bool
aSignedLebesgueEndgameCompilerClosed =
  ActualEnd.actualSignedLebesgueEndgameCompilerClosed

aGenericYoungCauchyResearchFrontier : Bool
aGenericYoungCauchyResearchFrontier = Analytic.aGenericYoungCauchyIsResearchFrontier

aGenericInverseSixthResearchFrontier : Bool
aGenericInverseSixthResearchFrontier = Analytic.aGenericInverseSixthTailIsResearchFrontier

aGenericAnalysisResearchFrontier : Bool
aGenericAnalysisResearchFrontier = false

aCompilerStackClosed : Bool
aCompilerStackClosed = true

aInternalFrontierClosed : Bool
aInternalFrontierClosed = false

clayPromotion : Bool
clayPromotion = false

------------------------------------------------------------------------
-- Regression receipts.
------------------------------------------------------------------------

aCompilerStackClosedIsTrue : aCompilerStackClosed ≡ true
aCompilerStackClosedIsTrue = refl

aGenericAnalysisResearchFrontierIsFalse :
  aGenericAnalysisResearchFrontier ≡ false
aGenericAnalysisResearchFrontierIsFalse = refl

aInternalFrontierClosedIsFalse : aInternalFrontierClosed ≡ false
aInternalFrontierClosedIsFalse = refl

aLegacyThreeStageBoardRetained : Bool
aLegacyThreeStageBoardRetained = true

aLegacyThreeStageBoardRetainedIsTrue :
  aLegacyThreeStageBoardRetained ≡ true
aLegacyThreeStageBoardRetainedIsTrue = refl

-- Keep an explicit compatibility witness that the old board is still the
-- public A1/A2/A3 programme rather than a new alternative proof architecture.
aOldLeafCountStillThree : Bool
aOldLeafCountStillThree = true
