module DASHI.Moonshine.OggSSPSmallCharacteristicExceptionalTermHypothesisSieveExact where

------------------------------------------------------------------------
-- SMALL-CHARACTERISTIC EXCEPTIONAL-TERM HYPOTHESIS SIEVE
--
-- PURPOSE
--
-- Record every serious prime-local statistic tested so far against the missing
-- Monster corrections
--
--   target(p=2) = 10,
--   target(p=3) =  2,
--
-- and make the negative results theorem-bearing.
--
-- IMPORTANT
--
-- The first six candidates below are independently defined by classical/wild
-- geometry or published p-adic analysis.  NONE matches both target values.
--
-- The final 10/2 "preferred finite payment" does match both, but it is a DASHI
-- candidate assembled from already selected local sectors/weights and is NOT
-- an independently constructed analytic valuation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.OggSSPSmallCharacteristicWildDifferentNoGoExact as Different
import DASHI.Moonshine.OggSSPSmallCharacteristicWildCanonicalCoefficientComparisonExact as Canonical
import DASHI.Moonshine.OggSSPSmallCharacteristicIndependentStatisticComparisonExact as Independent
import DASHI.Moonshine.OggSSPP2InertiaCentralizerValuationExact as P2Centralizer
import DASHI.Moonshine.OggSSPP3InertiaCentralizerValuationNoGoExact as P3Centralizer
import DASHI.Moonshine.OggSSPSmallCharacteristicDworkExplicitRootDepthNoGoExact as DworkRoot
import DASHI.Moonshine.OggSSPSmallCharacteristicPreferredCorrectionPaymentExact as Preferred
import DASHI.Moonshine.OggSSPSmallCharacteristicWildGeneratorPartitionCandidateExact as GeneratorPartition
import DASHI.Moonshine.OggSSPSmallCharacteristicWildLayerSectorProductCandidateExact as LayerSector
import DASHI.Moonshine.OggSSPSmallCharacteristicEtherealMultiplicityTransferExact as Ethereal
import DASHI.Moonshine.OggSSPSmallCharacteristicRigidifiedInertiaLayerProductNoGoExact as SameAmbient
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Target pair.
------------------------------------------------------------------------

record PrimePair : Set where
  constructor prime-pair
  field
    atTwo : Nat
    atThree : Nat

open PrimePair public

monsterExceptionalGapPair : PrimePair
monsterExceptionalGapPair =
  prime-pair 10 2

------------------------------------------------------------------------
-- 2. Independently defined statistics already tested.
------------------------------------------------------------------------

data IndependentStatistic : Set where
  rawWildDifferent :
    IndependentStatistic

  rigidifiedCanonicalMagnitude :
    IndependentStatistic

  evenRingGeneratorGap :
    IndependentStatistic

  inertiaCentralizerDepth :
    IndependentStatistic

  explicitDworkLiftedRootDepth :
    IndependentStatistic

  HasseWeight :
    IndependentStatistic

independentStatisticPair :
  IndependentStatistic ->
  PrimePair

independentStatisticPair rawWildDifferent =
  prime-pair
    Different.p2WildDifferentCoefficient
    Different.p3WildDifferentCoefficient

independentStatisticPair rigidifiedCanonicalMagnitude =
  prime-pair
    Canonical.p2RigidifiedCanonicalCoefficientMagnitude
    Canonical.p3RigidifiedCanonicalCoefficientMagnitude

independentStatisticPair evenRingGeneratorGap =
  prime-pair
    Independent.levelOneEvenGeneratorGap
    Independent.levelOneEvenGeneratorGap

independentStatisticPair inertiaCentralizerDepth =
  prime-pair
    P2Centralizer.p2UnorientedInertiaDepthSum
    P3Centralizer.p3UnorientedInertiaDepthSum

independentStatisticPair explicitDworkLiftedRootDepth =
  prime-pair
    DworkRoot.dworkP2LiftedRootDepth
    DworkRoot.dworkP3LiftedRootDepth

independentStatisticPair HasseWeight =
  prime-pair
    Independent.p2HasseWeight
    Independent.p3HasseWeight

------------------------------------------------------------------------
-- 3. Literal values.
------------------------------------------------------------------------

rawWildDifferentPair :
  independentStatisticPair rawWildDifferent
  ≡ prime-pair 14 7
rawWildDifferentPair = refl

canonicalMagnitudePair :
  independentStatisticPair rigidifiedCanonicalMagnitude
  ≡ prime-pair 10 5
canonicalMagnitudePair = refl

evenGeneratorGapPair :
  independentStatisticPair evenRingGeneratorGap
  ≡ prime-pair 10 10
evenGeneratorGapPair = refl

centralizerDepthPair :
  independentStatisticPair inertiaCentralizerDepth
  ≡ prime-pair 10 4
centralizerDepthPair = refl

dworkRootDepthPair :
  independentStatisticPair explicitDworkLiftedRootDepth
  ≡ prime-pair 8 3
dworkRootDepthPair = refl

hasseWeightPair :
  independentStatisticPair HasseWeight
  ≡ prime-pair 1 2
hasseWeightPair = refl

------------------------------------------------------------------------
-- 4. No independently defined statistic tested so far matches (10,2).
------------------------------------------------------------------------

data PairMatchesMonsterGap (pair : PrimePair) : Set where
  pair-matches-monster-gap :
    atTwo pair ≡ 10 ->
    atThree pair ≡ 2 ->
    PairMatchesMonsterGap pair

noKnownIndependentStatisticMatchesBoth :
  (statistic : IndependentStatistic) ->
  PairMatchesMonsterGap (independentStatisticPair statistic)
  ->
  ⊥
noKnownIndependentStatisticMatchesBoth rawWildDifferent
  (pair-matches-monster-gap () three)
noKnownIndependentStatisticMatchesBoth rigidifiedCanonicalMagnitude
  (pair-matches-monster-gap two ())
noKnownIndependentStatisticMatchesBoth evenRingGeneratorGap
  (pair-matches-monster-gap two ())
noKnownIndependentStatisticMatchesBoth inertiaCentralizerDepth
  (pair-matches-monster-gap two ())
noKnownIndependentStatisticMatchesBoth explicitDworkLiftedRootDepth
  (pair-matches-monster-gap () three)
noKnownIndependentStatisticMatchesBoth HasseWeight
  (pair-matches-monster-gap () three)

------------------------------------------------------------------------
-- 5. Prime-specific successes are retained rather than erased.
------------------------------------------------------------------------

p2CanonicalMagnitudeMatches :
  Canonical.p2RigidifiedCanonicalCoefficientMagnitude ≡ 10
p2CanonicalMagnitudeMatches = refl

p2GeneratorGapMatches :
  Independent.levelOneEvenGeneratorGap ≡ 10
p2GeneratorGapMatches = refl

p2CentralizerDepthMatches :
  P2Centralizer.p2UnorientedInertiaDepthSum ≡ 10
p2CentralizerDepthMatches = refl

p3HasseWeightMatches :
  Independent.p3HasseWeight ≡ 2
p3HasseWeightMatches = refl

------------------------------------------------------------------------
-- 5b. Cross-module structural candidates are graded separately.
------------------------------------------------------------------------

data CrossModuleStructuralCandidate : Set where
  wildGeneratorPartition :
    CrossModuleStructuralCandidate

  wildLayerTimesLocalSector :
    CrossModuleStructuralCandidate

structuralCandidatePair :
  CrossModuleStructuralCandidate ->
  PrimePair

structuralCandidatePair wildGeneratorPartition =
  prime-pair
    (GeneratorPartition.p2Candidate
      GeneratorPartition.canonicalGeneratorPartitionPair)
    (GeneratorPartition.p3Candidate
      GeneratorPartition.canonicalGeneratorPartitionPair)

structuralCandidatePair wildLayerTimesLocalSector =
  prime-pair
    (LayerSector.wildLayerSectorProduct LayerSector.wildTwo)
    (LayerSector.wildLayerSectorProduct LayerSector.wildThree)

generatorPartitionPairIsTenTwo :
  structuralCandidatePair wildGeneratorPartition
  ≡ prime-pair 10 2
generatorPartitionPairIsTenTwo = refl

wildLayerSectorPairIsTenTwo :
  structuralCandidatePair wildLayerTimesLocalSector
  ≡ prime-pair 10 2
wildLayerSectorPairIsTenTwo = refl

sameAmbientRigidifiedLayerInertiaPair : PrimePair
sameAmbientRigidifiedLayerInertiaPair =
  prime-pair
    SameAmbient.p2RigidifiedLayerInertiaProduct
    SameAmbient.p3RigidifiedLayerInertiaProduct

sameAmbientRigidifiedLayerInertiaPairIsSixThree :
  sameAmbientRigidifiedLayerInertiaPair
  ≡ prime-pair 6 3
sameAmbientRigidifiedLayerInertiaPairIsSixThree = refl

data SameAmbientRigidifiedLayerInertiaMatchesMonsterGap : Set where

sameAmbientRigidifiedLayerInertiaDoesNotMatchMonsterGap :
  SameAmbientRigidifiedLayerInertiaMatchesMonsterGap -> ⊥
sameAmbientRigidifiedLayerInertiaDoesNotMatchMonsterGap ()

generatorPartitionNeedsPrimeSelector :
  Bool
generatorPartitionNeedsPrimeSelector = true

wildLayerSectorUsesSameRuleAtBothPrimes :
  Bool
wildLayerSectorUsesSameRuleAtBothPrimes = true

data StructuralCandidateIsIndependentAnalyticValuation : Set where
data TenTwoStructuralMatchClosesMonsterBridge : Set where

structuralCandidateNotPromotedToIndependentAnalyticValuation :
  StructuralCandidateIsIndependentAnalyticValuation -> ⊥
structuralCandidateNotPromotedToIndependentAnalyticValuation ()

tenTwoStructuralMatchDoesNotCloseBridge :
  TenTwoStructuralMatchClosesMonsterBridge -> ⊥
tenTwoStructuralMatchDoesNotCloseBridge ()

------------------------------------------------------------------------
-- 6. The current preferred 10/2 finite payment is NOT classified as an
--    independently defined analytic statistic.
------------------------------------------------------------------------

preferredFinitePaymentPair : PrimePair
preferredFinitePaymentPair =
  prime-pair
    (Preferred.preferredTotal Preferred.wildTwo)
    (Preferred.preferredTotal Preferred.wildThree)

preferredFinitePaymentMatchesTarget :
  PairMatchesMonsterGap preferredFinitePaymentPair
preferredFinitePaymentMatchesTarget =
  pair-matches-monster-gap refl refl

data PreferredFinitePaymentIsIndependentAnalyticStatistic : Set where
data PrimeSpecificPartialMatchesSelectUniformAnalyticMechanism : Set where
data FailedUniformCandidatesProvePreferredFinitePayment : Set where

preferredFinitePaymentStillNotIndependentAnalyticStatistic :
  PreferredFinitePaymentIsIndependentAnalyticStatistic -> ⊥
preferredFinitePaymentStillNotIndependentAnalyticStatistic ()

partialMatchesDoNotSelectUniformMechanism :
  PrimeSpecificPartialMatchesSelectUniformAnalyticMechanism -> ⊥
partialMatchesDoNotSelectUniformMechanism ()

failedCandidatesDoNotProvePreferredPayment :
  FailedUniformCandidatesProvePreferredFinitePayment -> ⊥
failedCandidatesDoNotProvePreferredPayment ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryCrossModuleInference

record ExceptionalTermHypothesisSieveBoundary : Set where
  constructor exceptional-term-hypothesis-sieve-boundary
  field
    rawWildDifferentTested : Bool
    canonicalMagnitudeTested : Bool
    evenGeneratorGapTested : Bool
    centralizerDepthTested : Bool
    explicitDworkRootDepthTested : Bool
    HasseWeightTested : Bool
    noKnownIndependentStatisticMatchesBoth : Bool
    p2HasMultipleIndependentTenMatches : Bool
    p3HasseWeightTwoMatch : Bool
    generatorPartitionTenTwoMatchRecorded : Bool
    generatorPartitionSelectorDebtRecorded : Bool
    wildLayerSectorTenTwoMatchRecorded : Bool
    wildLayerSectorSameRuleAcrossPrimes : Bool
    wildLayerSectorUsesMixedAmbientObjects : Bool
    sameAmbientRigidifiedProductSixThreeRecorded : Bool
    sameAmbientRigidifiedProductRejected : Bool
    sourcedWildGeometryHasAdditiveModularMultiplicityPrecedent : Bool
    sourcedPrecedentIsLayerTimesSectorTheorem : Bool
    structuralCandidatesPromotedToAnalyticValuations : Bool
    preferredFinitePaymentMatchesTenTwo : Bool
    preferredFinitePaymentAlreadyIndependentAnalyticObject : Bool
    attributionFirewallPreserved : Bool

canonicalExceptionalTermHypothesisSieveBoundary :
  ExceptionalTermHypothesisSieveBoundary
canonicalExceptionalTermHypothesisSieveBoundary =
  record
    { rawWildDifferentTested = true
    ; canonicalMagnitudeTested = true
    ; evenGeneratorGapTested = true
    ; centralizerDepthTested = true
    ; explicitDworkRootDepthTested = true
    ; HasseWeightTested = true
    ; noKnownIndependentStatisticMatchesBoth = true
    ; p2HasMultipleIndependentTenMatches = true
    ; p3HasseWeightTwoMatch = true
    ; generatorPartitionTenTwoMatchRecorded = true
    ; generatorPartitionSelectorDebtRecorded = true
    ; wildLayerSectorTenTwoMatchRecorded = true
    ; wildLayerSectorSameRuleAcrossPrimes = true
    ; wildLayerSectorUsesMixedAmbientObjects = true
    ; sameAmbientRigidifiedProductSixThreeRecorded = true
    ; sameAmbientRigidifiedProductRejected = true
    ; sourcedWildGeometryHasAdditiveModularMultiplicityPrecedent = true
    ; sourcedPrecedentIsLayerTimesSectorTheorem = false
    ; structuralCandidatesPromotedToAnalyticValuations = false
    ; preferredFinitePaymentMatchesTenTwo = true
    ; preferredFinitePaymentAlreadyIndependentAnalyticObject = false
    ; attributionFirewallPreserved = true
    }
module DASHI.Moonshine.OggSSPSmallCharacteristicExceptionalTermHypothesisSieveExact where

------------------------------------------------------------------------
-- SMALL-CHARACTERISTIC EXCEPTIONAL-TERM HYPOTHESIS SIEVE
--
-- PURPOSE
--
-- Record every serious prime-local statistic tested so far against the missing
-- Monster corrections
--
--   target(p=2) = 10,
--   target(p=3) =  2,
--
-- and make the negative results theorem-bearing.
--
-- IMPORTANT
--
-- The first six candidates below are independently defined by classical/wild
-- geometry or published p-adic analysis.  NONE matches both target values.
--
-- The final 10/2 "preferred finite payment" does match both, but it is a DASHI
-- candidate assembled from already selected local sectors/weights and is NOT
-- an independently constructed analytic valuation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.OggSSPSmallCharacteristicWildDifferentNoGoExact as Different
import DASHI.Moonshine.OggSSPSmallCharacteristicWildCanonicalCoefficientComparisonExact as Canonical
import DASHI.Moonshine.OggSSPSmallCharacteristicIndependentStatisticComparisonExact as Independent
import DASHI.Moonshine.OggSSPP2InertiaCentralizerValuationExact as P2Centralizer
import DASHI.Moonshine.OggSSPP3InertiaCentralizerValuationNoGoExact as P3Centralizer
import DASHI.Moonshine.OggSSPSmallCharacteristicDworkExplicitRootDepthNoGoExact as DworkRoot
import DASHI.Moonshine.OggSSPSmallCharacteristicPreferredCorrectionPaymentExact as Preferred
import DASHI.Moonshine.OggSSPSmallCharacteristicWildGeneratorPartitionCandidateExact as GeneratorPartition
import DASHI.Moonshine.OggSSPSmallCharacteristicWildLayerSectorProductCandidateExact as LayerSector
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Target pair.
------------------------------------------------------------------------

record PrimePair : Set where
  constructor prime-pair
  field
    atTwo : Nat
    atThree : Nat

open PrimePair public

monsterExceptionalGapPair : PrimePair
monsterExceptionalGapPair =
  prime-pair 10 2

------------------------------------------------------------------------
-- 2. Independently defined statistics already tested.
------------------------------------------------------------------------

data IndependentStatistic : Set where
  rawWildDifferent :
    IndependentStatistic

  rigidifiedCanonicalMagnitude :
    IndependentStatistic

  evenRingGeneratorGap :
    IndependentStatistic

  inertiaCentralizerDepth :
    IndependentStatistic

  explicitDworkLiftedRootDepth :
    IndependentStatistic

  HasseWeight :
    IndependentStatistic

independentStatisticPair :
  IndependentStatistic ->
  PrimePair

independentStatisticPair rawWildDifferent =
  prime-pair
    Different.p2WildDifferentCoefficient
    Different.p3WildDifferentCoefficient

independentStatisticPair rigidifiedCanonicalMagnitude =
  prime-pair
    Canonical.p2RigidifiedCanonicalCoefficientMagnitude
    Canonical.p3RigidifiedCanonicalCoefficientMagnitude

independentStatisticPair evenRingGeneratorGap =
  prime-pair
    Independent.levelOneEvenGeneratorGap
    Independent.levelOneEvenGeneratorGap

independentStatisticPair inertiaCentralizerDepth =
  prime-pair
    P2Centralizer.p2UnorientedInertiaDepthSum
    P3Centralizer.p3UnorientedInertiaDepthSum

independentStatisticPair explicitDworkLiftedRootDepth =
  prime-pair
    DworkRoot.dworkP2LiftedRootDepth
    DworkRoot.dworkP3LiftedRootDepth

independentStatisticPair HasseWeight =
  prime-pair
    Independent.p2HasseWeight
    Independent.p3HasseWeight

------------------------------------------------------------------------
-- 3. Literal values.
------------------------------------------------------------------------

rawWildDifferentPair :
  independentStatisticPair rawWildDifferent
  ≡ prime-pair 14 7
rawWildDifferentPair = refl

canonicalMagnitudePair :
  independentStatisticPair rigidifiedCanonicalMagnitude
  ≡ prime-pair 10 5
canonicalMagnitudePair = refl

evenGeneratorGapPair :
  independentStatisticPair evenRingGeneratorGap
  ≡ prime-pair 10 10
evenGeneratorGapPair = refl

centralizerDepthPair :
  independentStatisticPair inertiaCentralizerDepth
  ≡ prime-pair 10 4
centralizerDepthPair = refl

dworkRootDepthPair :
  independentStatisticPair explicitDworkLiftedRootDepth
  ≡ prime-pair 8 3
dworkRootDepthPair = refl

hasseWeightPair :
  independentStatisticPair HasseWeight
  ≡ prime-pair 1 2
hasseWeightPair = refl

------------------------------------------------------------------------
-- 4. No independently defined statistic tested so far matches (10,2).
------------------------------------------------------------------------

data PairMatchesMonsterGap (pair : PrimePair) : Set where
  pair-matches-monster-gap :
    atTwo pair ≡ 10 ->
    atThree pair ≡ 2 ->
    PairMatchesMonsterGap pair

noKnownIndependentStatisticMatchesBoth :
  (statistic : IndependentStatistic) ->
  PairMatchesMonsterGap (independentStatisticPair statistic)
  ->
  ⊥
noKnownIndependentStatisticMatchesBoth rawWildDifferent
  (pair-matches-monster-gap () three)
noKnownIndependentStatisticMatchesBoth rigidifiedCanonicalMagnitude
  (pair-matches-monster-gap two ())
noKnownIndependentStatisticMatchesBoth evenRingGeneratorGap
  (pair-matches-monster-gap two ())
noKnownIndependentStatisticMatchesBoth inertiaCentralizerDepth
  (pair-matches-monster-gap two ())
noKnownIndependentStatisticMatchesBoth explicitDworkLiftedRootDepth
  (pair-matches-monster-gap () three)
noKnownIndependentStatisticMatchesBoth HasseWeight
  (pair-matches-monster-gap () three)

------------------------------------------------------------------------
-- 5. Prime-specific successes are retained rather than erased.
------------------------------------------------------------------------

p2CanonicalMagnitudeMatches :
  Canonical.p2RigidifiedCanonicalCoefficientMagnitude ≡ 10
p2CanonicalMagnitudeMatches = refl

p2GeneratorGapMatches :
  Independent.levelOneEvenGeneratorGap ≡ 10
p2GeneratorGapMatches = refl

p2CentralizerDepthMatches :
  P2Centralizer.p2UnorientedInertiaDepthSum ≡ 10
p2CentralizerDepthMatches = refl

p3HasseWeightMatches :
  Independent.p3HasseWeight ≡ 2
p3HasseWeightMatches = refl

------------------------------------------------------------------------
-- 5b. Cross-module structural candidates are graded separately.
------------------------------------------------------------------------

data CrossModuleStructuralCandidate : Set where
  wildGeneratorPartition :
    CrossModuleStructuralCandidate

  wildLayerTimesLocalSector :
    CrossModuleStructuralCandidate

structuralCandidatePair :
  CrossModuleStructuralCandidate ->
  PrimePair

structuralCandidatePair wildGeneratorPartition =
  prime-pair
    (GeneratorPartition.p2Candidate
      GeneratorPartition.canonicalGeneratorPartitionPair)
    (GeneratorPartition.p3Candidate
      GeneratorPartition.canonicalGeneratorPartitionPair)

structuralCandidatePair wildLayerTimesLocalSector =
  prime-pair
    (LayerSector.wildLayerSectorProduct LayerSector.wildTwo)
    (LayerSector.wildLayerSectorProduct LayerSector.wildThree)

generatorPartitionPairIsTenTwo :
  structuralCandidatePair wildGeneratorPartition
  ≡ prime-pair 10 2
generatorPartitionPairIsTenTwo = refl

wildLayerSectorPairIsTenTwo :
  structuralCandidatePair wildLayerTimesLocalSector
  ≡ prime-pair 10 2
wildLayerSectorPairIsTenTwo = refl

generatorPartitionNeedsPrimeSelector :
  Bool
generatorPartitionNeedsPrimeSelector = true

wildLayerSectorUsesSameRuleAtBothPrimes :
  Bool
wildLayerSectorUsesSameRuleAtBothPrimes = true

data StructuralCandidateIsIndependentAnalyticValuation : Set where
data TenTwoStructuralMatchClosesMonsterBridge : Set where

structuralCandidateNotPromotedToIndependentAnalyticValuation :
  StructuralCandidateIsIndependentAnalyticValuation -> ⊥
structuralCandidateNotPromotedToIndependentAnalyticValuation ()

tenTwoStructuralMatchDoesNotCloseBridge :
  TenTwoStructuralMatchClosesMonsterBridge -> ⊥
tenTwoStructuralMatchDoesNotCloseBridge ()

------------------------------------------------------------------------
-- 6. The current preferred 10/2 finite payment is NOT classified as an
--    independently defined analytic statistic.
------------------------------------------------------------------------

preferredFinitePaymentPair : PrimePair
preferredFinitePaymentPair =
  prime-pair
    (Preferred.preferredTotal Preferred.wildTwo)
    (Preferred.preferredTotal Preferred.wildThree)

preferredFinitePaymentMatchesTarget :
  PairMatchesMonsterGap preferredFinitePaymentPair
preferredFinitePaymentMatchesTarget =
  pair-matches-monster-gap refl refl

data PreferredFinitePaymentIsIndependentAnalyticStatistic : Set where
data PrimeSpecificPartialMatchesSelectUniformAnalyticMechanism : Set where
data FailedUniformCandidatesProvePreferredFinitePayment : Set where

preferredFinitePaymentStillNotIndependentAnalyticStatistic :
  PreferredFinitePaymentIsIndependentAnalyticStatistic -> ⊥
preferredFinitePaymentStillNotIndependentAnalyticStatistic ()

partialMatchesDoNotSelectUniformMechanism :
  PrimeSpecificPartialMatchesSelectUniformAnalyticMechanism -> ⊥
partialMatchesDoNotSelectUniformMechanism ()

failedCandidatesDoNotProvePreferredPayment :
  FailedUniformCandidatesProvePreferredFinitePayment -> ⊥
failedCandidatesDoNotProvePreferredPayment ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryCrossModuleInference

record ExceptionalTermHypothesisSieveBoundary : Set where
  constructor exceptional-term-hypothesis-sieve-boundary
  field
    rawWildDifferentTested : Bool
    canonicalMagnitudeTested : Bool
    evenGeneratorGapTested : Bool
    centralizerDepthTested : Bool
    explicitDworkRootDepthTested : Bool
    HasseWeightTested : Bool
    noKnownIndependentStatisticMatchesBoth : Bool
    p2HasMultipleIndependentTenMatches : Bool
    p3HasseWeightTwoMatch : Bool
    generatorPartitionTenTwoMatchRecorded : Bool
    generatorPartitionSelectorDebtRecorded : Bool
    wildLayerSectorTenTwoMatchRecorded : Bool
    wildLayerSectorSameNumericRuleAcrossPrimes : Bool
    wildLayerSectorUsesMixedAmbientObjects : Bool
    sameAmbientRigidifiedProductSixThreeRecorded : Bool
    sameAmbientRigidifiedProductRejected : Bool
    structuralCandidatesPromotedToAnalyticValuations : Bool
    preferredFinitePaymentMatchesTenTwo : Bool
    preferredFinitePaymentAlreadyIndependentAnalyticObject : Bool
    attributionFirewallPreserved : Bool

canonicalExceptionalTermHypothesisSieveBoundary :
  ExceptionalTermHypothesisSieveBoundary
canonicalExceptionalTermHypothesisSieveBoundary =
  exceptional-term-hypothesis-sieve-boundary
    true true true true true true
    true true true true true
    true true true true true
    false true false true
