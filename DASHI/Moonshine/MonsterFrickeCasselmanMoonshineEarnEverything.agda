module DASHI.Moonshine.MonsterFrickeCasselmanMoonshineEarnEverything where

------------------------------------------------------------------------
-- Cumulative convergence root.
--
-- Imports the live Monster/Fricke/Casselman highest-alpha theorem surface and
-- the modern recovery of PR #1's historical MoonshineEarn arithmetic.
--
-- Authority direction:
--
--   modern Monster/Fricke/JL/VOA theorem owners
--                  ^
--                  |
--         historical arithmetic weld
--
-- not the reverse.  In particular the FRACTRAN-style chain does not prove
-- Conway--Norton, VOA construction, or the Monster representation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.MonsterFrickeCasselmanHighestAlphaEverything as Current
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
