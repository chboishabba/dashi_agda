module DASHI.Moonshine.P11Level2ArithmeticGeometryHighestAlphaRegression where

open import DASHI.Core.Prelude

import DASHI.Moonshine.P11EichlerDeuringStackUnweightingExact as Stack
import DASHI.Moonshine.P11FullLevel2RigidificationExact as Level2
import DASHI.Moonshine.P11FullLevel2DeckHeckeEquivarianceExact as Deck
import DASHI.Moonshine.P11SupersingularLegendreLevel2ChartExact as Lambda
import DASHI.Moonshine.P11LegendreAnharmonicDeckExact as Anharmonic

stackCountEqualsLevel2Count :
  Stack.p11UnweightedStateCount ≡ Level2.p11FullLevel2RigidifiedCount
stackCountEqualsLevel2Count = refl

level2CountIsFive : Level2.p11FullLevel2RigidifiedCount ≡ 5
level2CountIsFive = Level2.p11FullLevel2RigidifiedCountIsFive

regularFrameS3Constructed :
  Level2.regularS3RelationsConstructed
    Level2.canonicalP11FullLevel2RigidificationBoundary
  ≡ true
regularFrameS3Constructed =
  Level2.regularS3RelationsConstructedIsTrue
    Level2.canonicalP11FullLevel2RigidificationBoundary

legendreFiveStateChartConstructed :
  Lambda.fiveStateCarrierIdentifiedWithSupersingularLegendreChart
    Lambda.canonicalP11SupersingularLegendreBoundary
  ≡ true
legendreFiveStateChartConstructed =
  Lambda.fiveStateCarrierIdentifiedWithSupersingularLegendreChartIsTrue
    Lambda.canonicalP11SupersingularLegendreBoundary

threeLinearRootsMapToJ1728 :
  Lambda.threeLinearRootsJ1728Certified
    Lambda.canonicalP11SupersingularLegendreBoundary
  ≡ true
threeLinearRootsMapToJ1728 =
  Lambda.threeLinearRootsJ1728CertifiedIsTrue
    Lambda.canonicalP11SupersingularLegendreBoundary

quadraticPairMapsToJZero :
  Lambda.quadraticFactorIdentifiedWithJZeroNumerator
    Lambda.canonicalP11SupersingularLegendreBoundary
  ≡ true
quadraticPairMapsToJZero =
  Lambda.quadraticFactorIdentifiedWithJZeroNumeratorIsTrue
    Lambda.canonicalP11SupersingularLegendreBoundary

frameDeckEqualsAnharmonicDeck :
  Anharmonic.anharmonicActionEqualsFrameDeckAction
    Anharmonic.canonicalP11LegendreAnharmonicDeckBoundary
  ≡ true
frameDeckEqualsAnharmonicDeck =
  Anharmonic.anharmonicActionEqualsFrameDeckActionIsTrue
    Anharmonic.canonicalP11LegendreAnharmonicDeckBoundary

oddHeckeAggregatesRespectLevel2Deck :
  Deck.oddR3R5AggregateDeckEquivarianceConstructed
    Deck.canonicalP11FullLevel2DeckHeckeBoundary
  ≡ true
oddHeckeAggregatesRespectLevel2Deck =
  Deck.oddR3R5AggregateDeckEquivarianceConstructedIsTrue
    Deck.canonicalP11FullLevel2DeckHeckeBoundary

individualOddHeckeEdgesStillOpen :
  Anharmonic.individualHeckeEdgesDerivedFromLambdaModularEquation
    Anharmonic.canonicalP11LegendreAnharmonicDeckBoundary
  ≡ false
individualOddHeckeEdgesStillOpen =
  Anharmonic.individualHeckeEdgesDerivedFromLambdaModularEquationIsFalse
    Anharmonic.canonicalP11LegendreAnharmonicDeckBoundary

ell2PrimeToLevelShortcutBlocked :
  Deck.ell2PrimeToLevelCompatibilityClaimed
    Deck.canonicalP11FullLevel2DeckHeckeBoundary
  ≡ false
ell2PrimeToLevelShortcutBlocked =
  Deck.ell2PrimeToLevelCompatibilityClaimedIsFalse
    Deck.canonicalP11FullLevel2DeckHeckeBoundary
