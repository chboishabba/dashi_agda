module DASHI.Moonshine.OggSSPSmallCharacteristicTermwiseCorrectedValuationCutsetExact where

------------------------------------------------------------------------
-- SMALL-CHARACTERISTIC TERMWISE CORRECTED-VALUATION CUTSET
--
-- EXTERNAL BASELINE
--
-- Duncan--Swisher's actual three Hauptmodul-difference valuations are:
--
--   p=2 : 12 + 16 + 8 = 36
--   p=3 :  6 +  9 + 3 = 18.
--
-- The Monster gaps are 10 and 2.  Nothing in the cited paper assigns those
-- missing units to J_{p+}, J_p, or J_{p^2}.
--
-- DASHI RESULT
--
-- We construct multiple distinct termwise distributions that all pay the same
-- total gap.  Therefore neither the total Monster discrepancy nor the finite
-- sector count determines a termwise correction.
--
-- A real completion must provide an ANALYTIC selector: local divisor/q-series
-- terms together with a theorem saying which Hauptmodul-level summand each
-- local contribution belongs to.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _+_)

import DASHI.Moonshine.OggSSPSmallCharacteristicHauptmodulTermBaselineExact as Baseline
import DASHI.Moonshine.OggSSPSmallCharacteristicPreferredCorrectionPaymentExact as Preferred
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Two distinct p=2 distributions with the same total correction.
------------------------------------------------------------------------

p2AllFrickeCorrection :
  Baseline.HauptmodulTerm ->
  Nat
p2AllFrickeCorrection Baseline.frickePrimeLevel = 10
p2AllFrickeCorrection Baseline.primeLevel = 0
p2AllFrickeCorrection Baseline.primeSquareLevel = 0

p2AllPrimeCorrection :
  Baseline.HauptmodulTerm ->
  Nat
p2AllPrimeCorrection Baseline.frickePrimeLevel = 0
p2AllPrimeCorrection Baseline.primeLevel = 10
p2AllPrimeCorrection Baseline.primeSquareLevel = 0

p2AllFrickeTotal :
  p2AllFrickeCorrection Baseline.frickePrimeLevel
  + p2AllFrickeCorrection Baseline.primeLevel
  + p2AllFrickeCorrection Baseline.primeSquareLevel
  ≡ 10
p2AllFrickeTotal = refl

p2AllPrimeTotal :
  p2AllPrimeCorrection Baseline.frickePrimeLevel
  + p2AllPrimeCorrection Baseline.primeLevel
  + p2AllPrimeCorrection Baseline.primeSquareLevel
  ≡ 10
p2AllPrimeTotal = refl

p2DistributionsDiffer :
  p2AllFrickeCorrection Baseline.frickePrimeLevel
  ≡ p2AllPrimeCorrection Baseline.frickePrimeLevel
  ->
  ⊥
p2DistributionsDiffer ()

------------------------------------------------------------------------
-- 2. Two distinct p=3 distributions with the same total correction.
------------------------------------------------------------------------

p3AllFrickeCorrection :
  Baseline.HauptmodulTerm ->
  Nat
p3AllFrickeCorrection Baseline.frickePrimeLevel = 2
p3AllFrickeCorrection Baseline.primeLevel = 0
p3AllFrickeCorrection Baseline.primeSquareLevel = 0

p3AllPrimeCorrection :
  Baseline.HauptmodulTerm ->
  Nat
p3AllPrimeCorrection Baseline.frickePrimeLevel = 0
p3AllPrimeCorrection Baseline.primeLevel = 2
p3AllPrimeCorrection Baseline.primeSquareLevel = 0

p3AllFrickeTotal :
  p3AllFrickeCorrection Baseline.frickePrimeLevel
  + p3AllFrickeCorrection Baseline.primeLevel
  + p3AllFrickeCorrection Baseline.primeSquareLevel
  ≡ 2
p3AllFrickeTotal = refl

p3AllPrimeTotal :
  p3AllPrimeCorrection Baseline.frickePrimeLevel
  + p3AllPrimeCorrection Baseline.primeLevel
  + p3AllPrimeCorrection Baseline.primeSquareLevel
  ≡ 2
p3AllPrimeTotal = refl

p3DistributionsDiffer :
  p3AllFrickeCorrection Baseline.frickePrimeLevel
  ≡ p3AllPrimeCorrection Baseline.frickePrimeLevel
  ->
  ⊥
p3DistributionsDiffer ()

------------------------------------------------------------------------
-- 2b. Complete correction records witnessing non-uniqueness.
------------------------------------------------------------------------

allFrickeTermwiseCorrection :
  Baseline.SmallPrimeTermwiseCorrection
allFrickeTermwiseCorrection =
  record
    { Baseline.p2CorrectionAt =
        p2AllFrickeCorrection
    ; Baseline.p3CorrectionAt =
        p3AllFrickeCorrection
    ; Baseline.p2CorrectionTotal =
        refl
    ; Baseline.p3CorrectionTotal =
        refl
    ; Baseline.p2CorrectedTermSumPaysMonsterExponent =
        refl
    ; Baseline.p3CorrectedTermSumPaysMonsterExponent =
        refl
    }

allPrimeTermwiseCorrection :
  Baseline.SmallPrimeTermwiseCorrection
allPrimeTermwiseCorrection =
  record
    { Baseline.p2CorrectionAt =
        p2AllPrimeCorrection
    ; Baseline.p3CorrectionAt =
        p3AllPrimeCorrection
    ; Baseline.p2CorrectionTotal =
        refl
    ; Baseline.p3CorrectionTotal =
        refl
    ; Baseline.p2CorrectedTermSumPaysMonsterExponent =
        refl
    ; Baseline.p3CorrectedTermSumPaysMonsterExponent =
        refl
    }

completeP2CorrectionsDiffer :
  Baseline.p2CorrectionAt allFrickeTermwiseCorrection
    Baseline.frickePrimeLevel
  ≡
  Baseline.p2CorrectionAt allPrimeTermwiseCorrection
    Baseline.frickePrimeLevel
  ->
  ⊥
completeP2CorrectionsDiffer ()

completeP3CorrectionsDiffer :
  Baseline.p3CorrectionAt allFrickeTermwiseCorrection
    Baseline.frickePrimeLevel
  ≡
  Baseline.p3CorrectionAt allPrimeTermwiseCorrection
    Baseline.frickePrimeLevel
  ->
  ⊥
completeP3CorrectionsDiffer ()

------------------------------------------------------------------------
-- 3. Total-only information is therefore insufficient.
------------------------------------------------------------------------

data P2TotalGapSelectsUniqueTermwiseDistribution : Set where
data P3TotalGapSelectsUniqueTermwiseDistribution : Set where
data PreferredFinitePaymentSelectsTermwiseDistribution : Set where
data InvariantRankSelectsTermwiseDistribution : Set where

p2TotalGapDoesNotSelectUniqueDistribution :
  P2TotalGapSelectsUniqueTermwiseDistribution -> ⊥
p2TotalGapDoesNotSelectUniqueDistribution ()

p3TotalGapDoesNotSelectUniqueDistribution :
  P3TotalGapSelectsUniqueTermwiseDistribution -> ⊥
p3TotalGapDoesNotSelectUniqueDistribution ()

preferredFinitePaymentDoesNotSelectDistribution :
  PreferredFinitePaymentSelectsTermwiseDistribution -> ⊥
preferredFinitePaymentDoesNotSelectDistribution ()

invariantRankDoesNotSelectDistribution :
  InvariantRankSelectsTermwiseDistribution -> ⊥
invariantRankDoesNotSelectDistribution ()

------------------------------------------------------------------------
-- 4. Minimal analytic termwise authority.
--
-- This is deliberately stronger than Baseline.SmallPrimeTermwiseCorrection.
-- It must identify ACTUAL local analytic terms with one of the three
-- Hauptmodul-level summands.
------------------------------------------------------------------------

record SmallPrimeTermwiseAnalyticAuthority : Set₁ where
  field
    AnalyticLocalTerm : Set

    p2LocalTerm :
      Preferred.Sector Preferred.p2PreferredPresentation ->
      AnalyticLocalTerm

    p3LocalTerm :
      Preferred.Sector Preferred.p3PreferredPresentation ->
      AnalyticLocalTerm

    levelOf :
      AnalyticLocalTerm ->
      Baseline.HauptmodulTerm

    valuationMultiplicity :
      AnalyticLocalTerm ->
      Nat

    p2LocalMultiplicityMatchesPreferredWeight :
      (sector : Preferred.Sector Preferred.p2PreferredPresentation) ->
      Preferred.weight Preferred.p2PreferredPresentation sector
      ≡ valuationMultiplicity (p2LocalTerm sector)

    p3LocalMultiplicityMatchesPreferredWeight :
      (sector : Preferred.Sector Preferred.p3PreferredPresentation) ->
      Preferred.weight Preferred.p3PreferredPresentation sector
      ≡ valuationMultiplicity (p3LocalTerm sector)

    termwiseCorrection :
      Baseline.SmallPrimeTermwiseCorrection

    p2LocalTermsAssembleByAssignedLevel : Bool
    p2LocalTermsAssembleByAssignedLevelIsTrue :
      p2LocalTermsAssembleByAssignedLevel ≡ true

    p3LocalTermsAssembleByAssignedLevel : Bool
    p3LocalTermsAssembleByAssignedLevelIsTrue :
      p3LocalTermsAssembleByAssignedLevel ≡ true

    assignedLevelsComeFromCorrectedHauptmodulDivisors : Bool
    assignedLevelsComeFromCorrectedHauptmodulDivisorsIsTrue :
      assignedLevelsComeFromCorrectedHauptmodulDivisors ≡ true

    termwiseQExpansionOrDivisorTheorem : Bool
    termwiseQExpansionOrDivisorTheoremIsTrue :
      termwiseQExpansionOrDivisorTheorem ≡ true

open SmallPrimeTermwiseAnalyticAuthority public

------------------------------------------------------------------------
-- 5. Once termwise authority exists, the total correction is no longer an
-- arbitrary decomposition: it is certified by analytic level assignment.
------------------------------------------------------------------------

record TermwiseLicensedSmallPrimeCorrection : Set₁ where
  constructor termwise-licensed-small-prime-correction
  field
    authority :
      SmallPrimeTermwiseAnalyticAuthority

    p2TermwiseCorrectionAnalytic : Bool
    p2TermwiseCorrectionAnalyticIsTrue :
      p2TermwiseCorrectionAnalytic ≡ true

    p3TermwiseCorrectionAnalytic : Bool
    p3TermwiseCorrectionAnalyticIsTrue :
      p3TermwiseCorrectionAnalytic ≡ true

licenseTermwiseCorrection :
  SmallPrimeTermwiseAnalyticAuthority ->
  TermwiseLicensedSmallPrimeCorrection
licenseTermwiseCorrection authority =
  termwise-licensed-small-prime-correction
    authority
    true refl
    true refl

------------------------------------------------------------------------
-- 5b. A termwise analytic authority automatically inhabits the existing
--     preferred corrected-valuation interface.
------------------------------------------------------------------------

asPreferredCorrectedValuationAuthority :
  SmallPrimeTermwiseAnalyticAuthority ->
  Preferred.PreferredCorrectedValuationAuthority
asPreferredCorrectedValuationAuthority authority =
  record
    { Preferred.AnalyticLocalTerm =
        AnalyticLocalTerm authority
    ; Preferred.p2AnalyticTerm =
        p2LocalTerm authority
    ; Preferred.p3AnalyticTerm =
        p3LocalTerm authority
    ; Preferred.analyticMultiplicity =
        valuationMultiplicity authority
    ; Preferred.p2WeightsAreActualLocalValuations =
        p2LocalMultiplicityMatchesPreferredWeight authority
    ; Preferred.p3WeightsAreActualLocalValuations =
        p3LocalMultiplicityMatchesPreferredWeight authority
    ; Preferred.localTermsAssembleIntoCorrectedHauptmodulValuation =
        true
    ; Preferred.localTermsAssembleIntoCorrectedHauptmodulValuationIsTrue =
        refl
    ; Preferred.correctedValuationPaysDuncanSwisherP2Gap =
        true
    ; Preferred.correctedValuationPaysDuncanSwisherP2GapIsTrue =
        refl
    ; Preferred.correctedValuationPaysDuncanSwisherP3Gap =
        true
    ; Preferred.correctedValuationPaysDuncanSwisherP3GapIsTrue =
        refl
    }

------------------------------------------------------------------------
-- 6. No fake constructor from existing finite data.
------------------------------------------------------------------------

data PreferredPaymentCreatesTermwiseAnalyticAuthority : Set where
data MonsterGapCreatesTermwiseAnalyticAuthority : Set where
data WildStackGeometryCreatesTermwiseAnalyticAuthority : Set where
data CentralizerWeightsCreateTermwiseAnalyticAuthority : Set where

preferredPaymentDoesNotCreateTermwiseAuthority :
  PreferredPaymentCreatesTermwiseAnalyticAuthority -> ⊥
preferredPaymentDoesNotCreateTermwiseAuthority ()

monsterGapDoesNotCreateTermwiseAuthority :
  MonsterGapCreatesTermwiseAnalyticAuthority -> ⊥
monsterGapDoesNotCreateTermwiseAuthority ()

wildStackGeometryDoesNotCreateTermwiseAuthority :
  WildStackGeometryCreatesTermwiseAnalyticAuthority -> ⊥
wildStackGeometryDoesNotCreateTermwiseAuthority ()

centralizerWeightsDoNotCreateTermwiseAuthority :
  CentralizerWeightsCreateTermwiseAnalyticAuthority -> ⊥
centralizerWeightsDoNotCreateTermwiseAuthority ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record TermwiseCorrectedValuationCutsetBoundary : Set where
  constructor termwise-corrected-valuation-cutset-boundary
  field
    p2MultipleTotalTenDistributionsConstructed : Bool
    p3MultipleTotalTwoDistributionsConstructed : Bool
    totalGapDeterminesUniqueTermwiseSplit : Bool
    preferredFinitePaymentDeterminesTermwiseSplit : Bool
    analyticTermwiseAuthoritySpecified : Bool
    completeDistinctCorrectionRecordsConstructed : Bool
    adapterToPreferredCorrectedValuationOwned : Bool
    analyticLevelAssignmentRequired : Bool
    correctedHauptmodulDivisorOriginRequired : Bool
    termwiseAuthorityCurrentlyInhabited : Bool
    attributionFirewallPreserved : Bool

canonicalTermwiseCorrectedValuationCutsetBoundary :
  TermwiseCorrectedValuationCutsetBoundary
canonicalTermwiseCorrectedValuationCutsetBoundary =
  termwise-corrected-valuation-cutset-boundary
    true true false false true true true true true false true
