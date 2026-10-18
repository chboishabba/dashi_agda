module DASHI.Moonshine.OggSSPSmallCharacteristicWildGeneratorPartitionCandidateExact where

------------------------------------------------------------------------
-- WILD MODULAR-FORM GENERATOR PARTITION CANDIDATE
--
-- EXTERNAL SOURCE SHAPE
--
-- Kobin--Zureick-Brown compute the even level-1 mod-p modular-form ring in
-- characteristics 2 and 3 with generator degrees 2 and 12:
--
--   M_even ~= k[x_2,x_12].
--
-- Consequently the source-derived numbers
--
--   lower generator degree = 2,
--   complementary degree gap = 12-2 = 10
--
-- exist independently of the Monster exponent.
--
-- DASHI OBSERVATION
--
-- The ordered pair
--
--   (complement, lower) = (10,2)
--
-- equals the exceptional Monster-gap pair (p=2,p=3).
--
-- CRITICAL SELECTOR DEBT
--
-- The same generator-degree pair (2,12) occurs in BOTH characteristics.
-- The source therefore does NOT itself select:
--
--   p=2 -> 12-2,
--   p=3 -> 2.
--
-- Any analytic promotion must supply a prime-sensitive geometric theorem
-- selecting those two different statistics.  Without such a selector this is
-- a cross-prime DASHI observation, not a valuation mechanism.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _-_)

import DASHI.Moonshine.OggSSPSmallCharacteristicIndependentStatisticComparisonExact as Independent
import DASHI.Moonshine.OggSSPSmallCharacteristicMonsterBridgeFailureLocalizationExact as Bridge
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Source-derived generator degrees.
------------------------------------------------------------------------

lowerEvenGeneratorDegree : Nat
lowerEvenGeneratorDegree =
  Independent.levelOneEvenLowerGeneratorWeight

upperEvenGeneratorDegree : Nat
upperEvenGeneratorDegree =
  Independent.levelOneDiscriminantGeneratorWeight

generatorComplement : Nat
generatorComplement =
  upperEvenGeneratorDegree - lowerEvenGeneratorDegree

lowerDegreeIsTwo :
  lowerEvenGeneratorDegree ≡ 2
lowerDegreeIsTwo = refl

upperDegreeIsTwelve :
  upperEvenGeneratorDegree ≡ 12
upperDegreeIsTwelve = refl

generatorComplementIsTen :
  generatorComplement ≡ 10
generatorComplementIsTen = refl

------------------------------------------------------------------------
-- 2. Cross-prime pair equals the Monster-bridge gaps.
------------------------------------------------------------------------

record GeneratorPartitionPair : Set where
  constructor generator-partition-pair
  field
    p2Candidate : Nat
    p3Candidate : Nat

open GeneratorPartitionPair public

canonicalGeneratorPartitionPair :
  GeneratorPartitionPair
canonicalGeneratorPartitionPair =
  generator-partition-pair
    generatorComplement
    lowerEvenGeneratorDegree

canonicalPairIsTenTwo :
  canonicalGeneratorPartitionPair
  ≡ generator-partition-pair 10 2
canonicalPairIsTenTwo = refl

p2CandidateMatchesBridgeGap :
  p2Candidate canonicalGeneratorPartitionPair
  ≡ Bridge.p2BridgeGap
p2CandidateMatchesBridgeGap = refl

p3CandidateMatchesBridgeGap :
  p3Candidate canonicalGeneratorPartitionPair
  ≡ Bridge.p3BridgeGap
p3CandidateMatchesBridgeGap = refl

------------------------------------------------------------------------
-- 3. The source does not select the cross-prime assignment.
------------------------------------------------------------------------

data WildPrime : Set where
  wildTwo wildThree : WildPrime

data GeneratorStatistic : Set where
  lowerDegree :
    GeneratorStatistic
  complementaryDegree :
    GeneratorStatistic

generatorStatisticValue :
  GeneratorStatistic ->
  Nat
generatorStatisticValue lowerDegree =
  lowerEvenGeneratorDegree
generatorStatisticValue complementaryDegree =
  generatorComplement

record PrimeSensitiveGeneratorSelector : Set where
  field
    select :
      WildPrime ->
      GeneratorStatistic

    p2SelectsComplement :
      select wildTwo ≡ complementaryDegree

    p3SelectsLower :
      select wildThree ≡ lowerDegree

    selectionDerivedFromIndependentGeometry : Bool
    selectionDerivedFromIndependentGeometryIsTrue :
      selectionDerivedFromIndependentGeometry ≡ true

    selectionProvedWithoutUsingMonsterGap : Bool
    selectionProvedWithoutUsingMonsterGapIsTrue :
      selectionProvedWithoutUsingMonsterGap ≡ true

open PrimeSensitiveGeneratorSelector public

------------------------------------------------------------------------
-- 4. A selector would produce the desired pair, but no selector is supplied.
------------------------------------------------------------------------

selectedGeneratorPayment :
  PrimeSensitiveGeneratorSelector ->
  WildPrime ->
  Nat
selectedGeneratorPayment selector prime =
  generatorStatisticValue (select selector prime)

selectorPaysP2Gap :
  (selector : PrimeSensitiveGeneratorSelector) ->
  selectedGeneratorPayment selector wildTwo
  ≡ Bridge.p2BridgeGap
selectorPaysP2Gap selector
  rewrite p2SelectsComplement selector =
  refl

selectorPaysP3Gap :
  (selector : PrimeSensitiveGeneratorSelector) ->
  selectedGeneratorPayment selector wildThree
  ≡ Bridge.p3BridgeGap
selectorPaysP3Gap selector
  rewrite p3SelectsLower selector =
  refl

------------------------------------------------------------------------
-- 5. Firewalls.
------------------------------------------------------------------------

data SameRingWeightsSelectPrimeSpecificStatistic : Set where
data OrderedTenTwoPairCreatesSelector : Set where
data GeneratorDegreesArePadicValuations : Set where
data GeneratorPartitionCreatesMonsterBridge : Set where
data KobinZureickBrownProposedMonsterCorrection : Set where

sameRingWeightsDoNotSelectPrimeSpecificStatistic :
  SameRingWeightsSelectPrimeSpecificStatistic -> ⊥
sameRingWeightsDoNotSelectPrimeSpecificStatistic ()

orderedPairDoesNotCreateSelector :
  OrderedTenTwoPairCreatesSelector -> ⊥
orderedPairDoesNotCreateSelector ()

generatorDegreesNotPromotedToPadicValuations :
  GeneratorDegreesArePadicValuations -> ⊥
generatorDegreesNotPromotedToPadicValuations ()

generatorPartitionDoesNotCreateMonsterBridge :
  GeneratorPartitionCreatesMonsterBridge -> ⊥
generatorPartitionDoesNotCreateMonsterBridge ()

kobinzureickBrownNotCreditedWithMonsterCorrection :
  KobinZureickBrownProposedMonsterCorrection -> ⊥
kobinzureickBrownNotCreditedWithMonsterCorrection ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryCrossModuleInference

record WildGeneratorPartitionCandidateBoundary : Set where
  constructor wild-generator-partition-candidate-boundary
  field
    sourcedLowerDegreeTwo : Bool
    sourcedUpperDegreeTwelve : Bool
    sourceDerivedComplementTen : Bool
    crossPrimeCandidatePairTenTwo : Bool
    candidatePairMatchesMonsterBridgeGaps : Bool
    sameGeneratorDegreesOccurAtBothPrimes : Bool
    independentPrimeSensitiveSelectorRequired : Bool
    independentPrimeSensitiveSelectorInhabited : Bool
    generatorDegreesPromotedToPadicValuation : Bool
    sourceCreditedWithMonsterCorrection : Bool
    attributionFirewallPreserved : Bool

canonicalWildGeneratorPartitionCandidateBoundary :
  WildGeneratorPartitionCandidateBoundary
canonicalWildGeneratorPartitionCandidateBoundary =
  wild-generator-partition-candidate-boundary
    true true true true true true true false false false true
