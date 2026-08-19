module DASHI.Moonshine.MoonshineEarnModernEverything where

------------------------------------------------------------------------
-- Focused recovery root for the historical PR #1 MoonshineEarn arithmetic.
--
-- The exact finite chain is retained:
--
--   7*11*23 -> 47*59*71 = 196883,
--   196883 + 1 = 196884.
--
-- Modern theorem owners then add three independent facts:
--
--   * all six source/target primes divide the actual Monster order;
--   * all six lie on the finite Fricke genus-zero control locus;
--   * the +1 in the weight-two Moonshine decomposition is the conformal line,
--     not an external observer.
--
-- The FRACTRAN chain itself is not promoted to a proof of Moonshine.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.MoonshineEarnHistoricalWeldExact as Earn
import DASHI.Moonshine.MoonshineOrbifoldWeightTwoDecompositionExact as Weight2

historicalTargetProductRegression : 47 * 59 * 71 ≡ 196883
historicalTargetProductRegression = Earn.historicalTargetProduct

historicalEarnChainRegression :
  (((7 * 11 * 23) / 23 * 47) / 7 * 59) / 11 * 71 ≡ 196883
historicalEarnChainRegression = Earn.historicalEarnChain

weightTwoEndpointRegression :
  47 * 59 * 71 + Weight2.conformalLineDimension
  ≡ Weight2.moonshineWeightTwoDimension
weightTwoEndpointRegression = Earn.historicalEndpointReconstructsModernWeightTwo

source7MonsterRegression : Earn.earnPrime Earn.source7 ≡ 7
source7MonsterRegression = refl

target71MonsterRegression : Earn.earnPrime Earn.target71 ≡ 71
target71MonsterRegression = refl

historicalObserverPromotionRejectedRegression :
  Earn.plusOneIdentifiedAsExternalObserver
    Earn.canonicalMoonshineEarnModernBoundary ≡ false
historicalObserverPromotionRejectedRegression = refl

fractranMoonshinePromotionRejectedRegression :
  Earn.fractranChainProvesConwayNorton
    Earn.canonicalMoonshineEarnModernBoundary ≡ false
fractranMoonshinePromotionRejectedRegression = refl
