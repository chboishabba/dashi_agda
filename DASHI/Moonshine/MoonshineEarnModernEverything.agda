module DASHI.Moonshine.MoonshineEarnModernEverything where

------------------------------------------------------------------------
-- Focused recovery root for the historical PR #1 MoonshineEarn arithmetic.
--
-- The exact finite chain is retained:
--
--   7*11*23 -> 47*59*71 = 196883,
--   196883 + 1 = 196884.
--
-- Modern theorem owners add independent facts:
--
--   * all six source/target primes divide the actual Monster order;
--   * all six lie on the finite Fricke genus-zero control locus;
--   * the +1 in the weight-two Moonshine decomposition is the conformal line,
--     not an external observer.
--
-- Exact mechanistic falsifiers kill four obvious interpretations:
--
--   * not a Monster conjugacy-class power map;
--   * not Fricke level motion;
--   * not routing by shared Ogg/Monster support alone;
--   * not one uniform source-prime cyclic-normalizer mechanism.
--
-- The quantitative exponent observer now supplies a genuinely finer positive
-- result.  On the three historical SOURCES,
--
--   v_23=1, v_7=6, v_11=2,
--
-- so exponent strictly refines the constant Ogg observer and separates the
-- source carrier.  The historical targets therefore factor through source
-- exponent on this three-point dataset.  But exponent is NOT conserved: the
-- target exponents at 47,59,71 are all one.  This factorization is a surviving
-- discriminator, not a claimed Moonshine dynamics or causal explanation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.MoonshineEarnHistoricalWeldExact as Earn
import DASHI.Moonshine.MoonshineOrbifoldWeightTwoDecompositionExact as Weight2
import DASHI.Moonshine.MoonshineEarnPowerMapNoGoExact as PowerNoGo
import DASHI.Moonshine.MoonshineEarnFrickeLevelNoGoExact as FrickeNoGo
import DASHI.Moonshine.MoonshineEarnOggObserverNonfactorabilityExact as ObserverNoGo
import DASHI.Moonshine.MoonshineEarnCyclicNormalizerNoGoExact as NormalizerNoGo
import DASHI.Moonshine.MoonshineEarnExponentObserverFactorizationExact as ExponentObserver

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

------------------------------------------------------------------------
-- Surviving finer observer: source Monster exponent.
------------------------------------------------------------------------

sourceExponentStrictlyRefinesOggRegression :
  ExponentObserver.exponentStrictlyRefinesOggOnHistoricalSources
    ExponentObserver.canonicalMoonshineEarnExponentObserverBoundary ≡ true
sourceExponentStrictlyRefinesOggRegression = refl

sourceExponentRoutesHistoricalTargetsRegression :
  ExponentObserver.historicalRoutingFactorsThroughSourceExponent
    ExponentObserver.canonicalMoonshineEarnExponentObserverBoundary ≡ true
sourceExponentRoutesHistoricalTargetsRegression = refl

historicalRoutingDoesNotConserveExponentRegression :
  ExponentObserver.routingUniformlyPreservesMonsterExponent
    ExponentObserver.canonicalMoonshineEarnExponentObserverBoundary ≡ false
historicalRoutingDoesNotConserveExponentRegression = refl

factorizationIsNotMechanismRegression :
  ExponentObserver.factorizationProvesMoonshineMechanism
    ExponentObserver.canonicalMoonshineEarnExponentObserverBoundary ≡ false
factorizationIsNotMechanismRegression = refl

------------------------------------------------------------------------
-- Updated frontier: Ogg support is too coarse, exponent is sufficient to route
-- the three source examples, but not conserved.  Any deeper interpretation must
-- explain WHY that discriminator is selected rather than merely fit the three
-- finite points.
------------------------------------------------------------------------

finerMoonshineCoordinateStillRequiredForMechanismRegression :
  ObserverNoGo.finerMoonshineCoordinateRequiredForMechanism
    ObserverNoGo.canonicalMoonshineEarnOggObserverBoundary ≡ true
finerMoonshineCoordinateStillRequiredForMechanismRegression = refl
