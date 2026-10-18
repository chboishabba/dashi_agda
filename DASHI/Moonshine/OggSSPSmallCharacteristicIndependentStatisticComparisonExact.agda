module DASHI.Moonshine.OggSSPSmallCharacteristicIndependentStatisticComparisonExact where

------------------------------------------------------------------------
-- INDEPENDENT SMALL-PRIME GEOMETRIC/STACK STATISTIC COMPARISON
--
-- EXTERNAL GEOMETRY / MODULAR-FORM INPUT
--
-- Kobin--Zureick-Brown compute:
--
--   char 3 : M_even ~= k[x_2,x_12],
--            Hasse invariant has weight 2,
--            |canonical coefficient on X(1)^rig| = 5.
--
--   char 2 : M_even ~= k[x_2,x_12],
--            Hasse invariant has weight 1,
--            |canonical coefficient on X(1)^rig| = 10.
--
-- DASHI CROSS-CHECK
--
-- p=2:
--   generator-degree gap 12-2 = 10,
--   canonical coefficient magnitude = 10,
--   preferred inertia-centralizer statistic = 10,
--   Monster exceptional gap = 10.
--
-- p=3:
--   Hasse weight = 2,
--   local-incidence orbit rank = 2,
--   Monster exceptional gap = 2,
--   while generator-degree gap = 10,
--         canonical magnitude = 5,
--         inertia-centralizer statistic = 4.
--
-- This module records the pattern and blocks any inference that one uniform
-- formula has thereby been proved.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; _-_)

import DASHI.Moonshine.OggSSPSmallCharacteristicWildCanonicalCoefficientComparisonExact as Canonical
import DASHI.Moonshine.OggSSPSmallCharacteristicCorrectionMechanismComparisonExact as Mechanism
import DASHI.Moonshine.OggSSPSmallCharacteristicPreferredCorrectionPaymentExact as Preferred
import DASHI.Moonshine.OggSSPP3InertiaCentralizerValuationNoGoExact as P3Centralizer
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Sourced modular-form generator weights.
------------------------------------------------------------------------

levelOneEvenLowerGeneratorWeight : Nat
levelOneEvenLowerGeneratorWeight = 2

levelOneDiscriminantGeneratorWeight : Nat
levelOneDiscriminantGeneratorWeight = 12

levelOneEvenGeneratorGap : Nat
levelOneEvenGeneratorGap =
  levelOneDiscriminantGeneratorWeight
  - levelOneEvenLowerGeneratorWeight

levelOneEvenGeneratorGapIsTen :
  levelOneEvenGeneratorGap ≡ 10
levelOneEvenGeneratorGapIsTen = refl

p2HasseWeight : Nat
p2HasseWeight = 1

p3HasseWeight : Nat
p3HasseWeight = 2

------------------------------------------------------------------------
-- 2. p=2 independent ten-fold coincidence surface.
------------------------------------------------------------------------

p2CanonicalMagnitudeIsTen :
  Canonical.p2RigidifiedCanonicalCoefficientMagnitude ≡ 10
p2CanonicalMagnitudeIsTen = refl

p2GeneratorGapIsTen :
  levelOneEvenGeneratorGap ≡ 10
p2GeneratorGapIsTen = refl

p2PreferredLocalStatisticIsTen :
  Preferred.preferredTotal Preferred.wildTwo ≡ 10
p2PreferredLocalStatisticIsTen = refl

p2MonsterGapIsTen :
  Canonical.p2MonsterExceptionalGap ≡ 10
p2MonsterGapIsTen = refl

p2CanonicalEqualsGeneratorGap :
  Canonical.p2RigidifiedCanonicalCoefficientMagnitude
  ≡ levelOneEvenGeneratorGap
p2CanonicalEqualsGeneratorGap = refl

p2CanonicalEqualsPreferredLocalStatistic :
  Canonical.p2RigidifiedCanonicalCoefficientMagnitude
  ≡ Preferred.preferredTotal Preferred.wildTwo
p2CanonicalEqualsPreferredLocalStatistic = refl

------------------------------------------------------------------------
-- 3. p=3 independent two-fold support and competing failed statistics.
------------------------------------------------------------------------

p3HasseWeightIsTwo :
  p3HasseWeight ≡ 2
p3HasseWeightIsTwo = refl

p3PreferredLocalOrbitStatisticIsTwo :
  Preferred.preferredTotal Preferred.wildThree ≡ 2
p3PreferredLocalOrbitStatisticIsTwo = refl

p3MonsterGapIsTwo :
  Canonical.p3MonsterExceptionalGap ≡ 2
p3MonsterGapIsTwo = refl

p3HasseWeightEqualsPreferredLocalStatistic :
  p3HasseWeight
  ≡ Preferred.preferredTotal Preferred.wildThree
p3HasseWeightEqualsPreferredLocalStatistic = refl

p3GeneratorGapIsNotMonsterGap :
  levelOneEvenGeneratorGap
  ≡ Canonical.p3MonsterExceptionalGap
  ->
  ⊥
p3GeneratorGapIsNotMonsterGap ()

p3CanonicalMagnitudeIsNotMonsterGap :
  Canonical.p3RigidifiedCanonicalCoefficientMagnitude
  ≡ Canonical.p3MonsterExceptionalGap
  ->
  ⊥
p3CanonicalMagnitudeIsNotMonsterGap ()

p3CentralizerDepthIsNotMonsterGap :
  P3Centralizer.p3UnorientedInertiaDepthSum
  ≡ Canonical.p3MonsterExceptionalGap
  ->
  ⊥
p3CentralizerDepthIsNotMonsterGap ()

------------------------------------------------------------------------
-- 4. Wrong-type / attribution guards.
------------------------------------------------------------------------

data IndependentNumericalMatchesProveAnalyticFourthTerm : Set where
data SameLevelOneRingForP2P3ImpliesSameCorrectionFormula : Set where
data GeneratorWeightIsPadicValuation : Set where
data CanonicalDivisorCoefficientIsPadicValuation : Set where

independentMatchesDoNotProveAnalyticFourthTerm :
  IndependentNumericalMatchesProveAnalyticFourthTerm -> ⊥
independentMatchesDoNotProveAnalyticFourthTerm ()

sameLevelOneRingDoesNotForceUniformCorrection :
  SameLevelOneRingForP2P3ImpliesSameCorrectionFormula -> ⊥
sameLevelOneRingDoesNotForceUniformCorrection ()

generatorWeightIsNotPromotedToPadicValuation :
  GeneratorWeightIsPadicValuation -> ⊥
generatorWeightIsNotPromotedToPadicValuation ()

canonicalCoefficientIsNotPromotedToPadicValuation :
  CanonicalDivisorCoefficientIsPadicValuation -> ⊥
canonicalCoefficientIsNotPromotedToPadicValuation ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryCrossModuleInference

record IndependentStatisticComparisonBoundary : Set where
  constructor independent-statistic-comparison-boundary
  field
    p2CanonicalMagnitudeTen : Bool
    p2EvenGeneratorGapTen : Bool
    p2PreferredLocalStatisticTen : Bool
    p2ThreeIndependentStatisticsAgree : Bool
    p3HasseWeightTwo : Bool
    p3PreferredLocalOrbitStatisticTwo : Bool
    p3GeneratorGapTenRejected : Bool
    p3CanonicalMagnitudeFiveRejected : Bool
    p3CentralizerDepthFourRejected : Bool
    uniformCorrectionFormulaDerived : Bool
    analyticFourthTermDerived : Bool
    attributionFirewallPreserved : Bool

canonicalIndependentStatisticComparisonBoundary :
  IndependentStatisticComparisonBoundary
canonicalIndependentStatisticComparisonBoundary =
  independent-statistic-comparison-boundary
    true true true true
    true true true true true
    false false true
