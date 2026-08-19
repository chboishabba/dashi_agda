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
-- This root now also carries exact mechanistic falsifiers for the historical
-- substitution itself:
--
--   * it cannot be a Monster conjugacy-class POWER MAP, because ord(g^k)
--     divides ord(g), while 23->47, 7->59, 11->71 increase prime order;
--   * it cannot be a Fricke involution / Fricke level motion, because W_p acts
--     inside the fixed level p;
--   * it cannot factor through the shared Monster/Ogg/Fricke genus-zero
--     membership observer, because all three sources have the same coarse
--     observation but require three different targets;
--   * it cannot uniformly be a source-prime cyclic complement acting on the
--     target prime subgroup: 23|46 passes, but 7∤58 and 11∤70.
--
-- Thus the surviving historical research question is genuinely finer:
-- if the arithmetic has a Moonshine mechanism, it must live in structure such
-- as class/character/modular-function data beyond Ogg membership, and it is not
-- any of the standard operations excluded above.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.MoonshineEarnHistoricalWeldExact as Earn
import DASHI.Moonshine.MoonshineOrbifoldWeightTwoDecompositionExact as Weight2
import DASHI.Moonshine.MoonshineEarnPowerMapNoGoExact as PowerNoGo
import DASHI.Moonshine.MoonshineEarnFrickeLevelNoGoExact as FrickeNoGo
import DASHI.Moonshine.MoonshineEarnOggObserverNonfactorabilityExact as ObserverNoGo
import DASHI.Moonshine.MoonshineEarnCyclicNormalizerNoGoExact as NormalizerNoGo

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

------------------------------------------------------------------------
-- Mechanistic falsifier regressions.
------------------------------------------------------------------------

directMonsterPowerMapRejectedRegression :
  PowerNoGo.directMonsterPowerMapInterpretationPossible
    PowerNoGo.canonicalMoonshineEarnPowerMapNoGoBoundary ≡ false
directMonsterPowerMapRejectedRegression = refl

directReplicabilityPowerMapRejectedRegression :
  PowerNoGo.directReplicabilityPowerMapExplanationPossible
    PowerNoGo.canonicalMoonshineEarnPowerMapNoGoBoundary ≡ false
directReplicabilityPowerMapRejectedRegression = refl

directFrickeMotionRejectedRegression :
  FrickeNoGo.directFrickeInvolutionExplanationPossible
    FrickeNoGo.canonicalMoonshineEarnFrickeLevelNoGoBoundary ≡ false
directFrickeMotionRejectedRegression = refl

oggMembershipCannotRouteEarnTargetsRegression :
  ObserverNoGo.substitutionFactorsThroughOggMembership
    ObserverNoGo.canonicalMoonshineEarnOggObserverBoundary ≡ false
oggMembershipCannotRouteEarnTargetsRegression = refl

uniformCyclicNormalizerRejectedRegression :
  NormalizerNoGo.uniformCyclicNormalizerExplanationPossible
    NormalizerNoGo.canonicalMoonshineEarnCyclicNormalizerBoundary ≡ false
uniformCyclicNormalizerRejectedRegression = refl

firstNormalizerEdgeOnlyNecessaryConditionRegression :
  NormalizerNoGo.firstEdgePromotedToMonsterSubgroupTheorem
    NormalizerNoGo.canonicalMoonshineEarnCyclicNormalizerBoundary ≡ false
firstNormalizerEdgeOnlyNecessaryConditionRegression = refl

finerMoonshineCoordinateStillRequiredRegression :
  ObserverNoGo.finerMoonshineCoordinateRequiredForMechanism
    ObserverNoGo.canonicalMoonshineEarnOggObserverBoundary ≡ true
finerMoonshineCoordinateStillRequiredRegression = refl
