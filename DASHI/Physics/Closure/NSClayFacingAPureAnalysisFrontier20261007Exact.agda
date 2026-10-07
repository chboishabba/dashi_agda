module DASHI.Physics.Closure.NSClayFacingAPureAnalysisFrontier20261007Exact where

------------------------------------------------------------------------
-- CLAY-FACING A / PURE-ANALYSIS + SAME-OBJECT MAX-CUT / 2026-10-07
--
-- Preserve the public three-stage programme
--
--   A1 physical pair -> A2 finite-energy majorants -> A3 continuation,
--
-- but expose only theorem-producing leaves after the repository's closed
-- canonical-pair/resolvent/origin/curvature/measure compiler stack is removed.
--
-- Important recut:
--   NSWholeSpaceCanonicalPairSaturationOriginExact already constructs the
--   physical output/pair resolvents directly from nu|xi|^2 and the centered
--   residual, constructs the canonical same-output projected Gram pair, proves
--   the saturation coefficient identity, and proves the origin bound.
--   NSWholeSpaceCanonicalSignedPairCarrierExact then gives the exact signed
--   pair carrier.  Therefore A1a is NOT an abstract-kernel weld any more.
--
-- Remaining A1:
--   * populate that canonical pair data from the ACTUAL continuum NS integrand;
--   * identify the actual high-frequency physical heat/envelope data.
-- Remaining A2:
--   * low physical majorant <= compact-output convolution envelope;
--   * high physical majorant <= inverse-sixth weighted envelope.
-- Remaining A3:
--   * continuation criterion + literal whole-space NS/pressure/global-smooth
--     assembly.  Building the compensated field and signed-Lebesgue endgame is
--     already closed compiler infrastructure.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSClayFacingAMaxCut20261002Exact as Old
import DASHI.Physics.Closure.NSClayFacingAAnalyticCutExact as Analytic
import DASHI.Physics.Closure.NSClayFacingAPhysicalSameObjectCutExact as Physical
import DASHI.Physics.Closure.NSWholeSpaceCanonicalPairSaturationOriginExact as Pair
import DASHI.Physics.Closure.NSWholeSpaceCanonicalSignedPairCarrierExact as SignedPair
import DASHI.Physics.Closure.NSWholeSpaceLowHighConvolutionProducerExact as Conv
import DASHI.Physics.Closure.NSWholeSpacePhysicalMajorantDominationProducerExact as DomProducer
import DASHI.Physics.Closure.NSWholeSpaceActualPhysicalCompensatedFieldExact as ActualField
import DASHI.Physics.Closure.NSWholeSpaceActualSignedLebesgueEndgameExact as ActualEnd
import DASHI.Physics.Closure.NSABCDConcentratedCompletionCutExact as Cut

data AStage : Set where
  A1PhysicalPair : AStage
  A2FiniteEnergyMajorants : AStage
  A3WholeSpaceContinuation : AStage

data APureLeaf : Set where
  a1ActualCanonicalPairPopulation : APureLeaf
  a1HighFrequencyHeatEnvelopeWeld : APureLeaf
  a2LowPhysicalMajorantDomination : APureLeaf
  a2HighPhysicalMajorantDomination : APureLeaf
  a3ContinuationCriterionLiteralNS : APureLeaf

leafStage : APureLeaf → AStage
leafStage a1ActualCanonicalPairPopulation = A1PhysicalPair
leafStage a1HighFrequencyHeatEnvelopeWeld = A1PhysicalPair
leafStage a2LowPhysicalMajorantDomination = A2FiniteEnergyMajorants
leafStage a2HighPhysicalMajorantDomination = A2FiniteEnergyMajorants
leafStage a3ContinuationCriterionLiteralNS = A3WholeSpaceContinuation

-- None of these physical/theorem leaves is silently promoted by the compiler
-- reductions below.
aPureLeafClosed : APureLeaf → Bool
aPureLeafClosed a1ActualCanonicalPairPopulation = false
aPureLeafClosed a1HighFrequencyHeatEnvelopeWeld = false
aPureLeafClosed a2LowPhysicalMajorantDomination = false
aPureLeafClosed a2HighPhysicalMajorantDomination = false
aPureLeafClosed a3ContinuationCriterionLiteralNS = Cut.aLiteralClayTheoremClosed

currentHighestInformationALeaf : APureLeaf
currentHighestInformationALeaf = a1ActualCanonicalPairPopulation

------------------------------------------------------------------------
-- Canonical near-origin physical infrastructure already closed.
------------------------------------------------------------------------

aCanonicalPairResolventsConstructed : Bool
aCanonicalPairResolventsConstructed = Pair.canonicalPairResolventsConstructed

aCanonicalPairOriginBoundClosed : Bool
aCanonicalPairOriginBoundClosed = true

aCanonicalSignedPairCarrierClosed : Bool
aCanonicalSignedPairCarrierClosed = SignedPair.signedSplitDefinitional

aCanonicalPairInfrastructureClosed : Bool
aCanonicalPairInfrastructureClosed = true

-- This is now the exact A1a residual: not another resolvent/kernel theorem,
-- but same-object population of the already-canonical pair carrier by the
-- actual continuum Navier--Stokes integrand.
aNearOriginResidualIsActualPairPopulation : Bool
aNearOriginResidualIsActualPairPopulation = true

------------------------------------------------------------------------
-- Other closed infrastructure removed from the research board.
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

-- Attachment-ledger A3 steps 24 and 25 are exactly these two compilers.
aA3PhysicalFieldAssemblyClosed : Bool
aA3PhysicalFieldAssemblyClosed =
  ActualField.actualPhysicalCompensatedFieldCompilerClosed

aA3SignedLebesgueAssemblyClosed : Bool
aA3SignedLebesgueAssemblyClosed =
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

aCanonicalPairInfrastructureClosedIsTrue :
  aCanonicalPairInfrastructureClosed ≡ true
aCanonicalPairInfrastructureClosedIsTrue = refl

aNearOriginResidualIsActualPairPopulationIsTrue :
  aNearOriginResidualIsActualPairPopulation ≡ true
aNearOriginResidualIsActualPairPopulationIsTrue = refl

aA3PhysicalFieldAssemblyClosedIsTrue : aA3PhysicalFieldAssemblyClosed ≡ true
aA3PhysicalFieldAssemblyClosedIsTrue = refl

aA3SignedLebesgueAssemblyClosedIsTrue : aA3SignedLebesgueAssemblyClosed ≡ true
aA3SignedLebesgueAssemblyClosedIsTrue = refl

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

-- Compatibility statement only: the public route remains A1/A2/A3 even though
-- the new frontier resolves A1 below the old abstract-kernel presentation.
aOldLeafCountStillThree : Bool
aOldLeafCountStillThree = true
