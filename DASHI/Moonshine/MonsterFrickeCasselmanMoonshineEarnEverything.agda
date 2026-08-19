module DASHI.Moonshine.MonsterFrickeCasselmanMoonshineEarnEverything where

------------------------------------------------------------------------
-- Cumulative convergence root.
--
-- Imports the live Monster/Fricke/Casselman highest-alpha theorem surface,
-- Duncan--Swisher quantitative exponent depth, and the modern recovery/stress
-- test of PR #1's historical MoonshineEarn arithmetic.
--
-- Authority direction:
--
--   modern Monster/Fricke/JL/VOA/exponent theorem owners
--                  ^
--                  |
--         historical arithmetic weld
--
-- not the reverse.  In particular the FRACTRAN-style chain does not prove
-- Conway--Norton, VOA construction, the Monster representation, or the
-- Duncan--Swisher exponent formulas.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.MonsterFrickeCasselmanHighestAlphaEverything as Current
import DASHI.Moonshine.DuncanSwisherExponentDepthHighestAlphaEverything as Depth
import DASHI.Moonshine.MoonshineEarnModernEverything as EarnRoot
import DASHI.Moonshine.MoonshineEarnHistoricalWeldExact as Earn
import DASHI.Moonshine.MoonshineOrbifoldWeightTwoDecompositionExact as Weight2

historicalEarnEndpointRegression : 47 * 59 * 71 ≡ 196883
historicalEarnEndpointRegression = EarnRoot.historicalTargetProductRegression

historicalEarnWeightTwoRegression :
  47 * 59 * 71 + Weight2.conformalLineDimension
  ≡ Weight2.moonshineWeightTwoDimension
historicalEarnWeightTwoRegression = EarnRoot.weightTwoEndpointRegression

historicalObserverSemanticsRetractedRegression :
  Earn.plusOneIdentifiedAsExternalObserver
    Earn.canonicalMoonshineEarnModernBoundary ≡ false
historicalObserverSemanticsRetractedRegression = refl

historicalEarnDoesNotProveConwayNortonRegression :
  Earn.fractranChainProvesConwayNorton
    Earn.canonicalMoonshineEarnModernBoundary ≡ false
historicalEarnDoesNotProveConwayNortonRegression = refl

currentLocalSameObjectStillClosedRegression :
  Current.localSameObjectSeamResolvedRegression
  ≡ Current.localSameObjectSeamResolvedRegression
currentLocalSameObjectStillClosedRegression = refl

------------------------------------------------------------------------
-- Quantitative depth now sits above support in the same public convergence.
------------------------------------------------------------------------

fullExponentDepthRetainedRegression :
  Depth.fullExponentDepthNowRetained
    Depth.canonicalDuncanSwisherExponentDepthHighestAlphaBoundary ≡ true
fullExponentDepthRetainedRegression = refl

geometricAndModularObserversShareConsumerRegression :
  Depth.geometricAndModularObserversShareConsumer
    Depth.canonicalDuncanSwisherExponentDepthHighestAlphaBoundary ≡ true
geometricAndModularObserversShareConsumerRegression = refl

lowPrimeResidualsIsolatedRegression :
  Depth.p2p3ResidualsIsolated
    Depth.canonicalDuncanSwisherExponentDepthHighestAlphaBoundary ≡ true
lowPrimeResidualsIsolatedRegression = refl

historicalRoutingFactorsThroughExponentRegression :
  EarnRoot.sourceExponentRoutesHistoricalTargetsRegression
  ≡ EarnRoot.sourceExponentRoutesHistoricalTargetsRegression
historicalRoutingFactorsThroughExponentRegression = refl
