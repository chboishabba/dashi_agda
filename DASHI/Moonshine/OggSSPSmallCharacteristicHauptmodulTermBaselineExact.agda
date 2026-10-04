module DASHI.Moonshine.OggSSPSmallCharacteristicHauptmodulTermBaselineExact where

------------------------------------------------------------------------
-- DUNCAN--SWISHER SMALL-PRIME THREE-TERM BASELINE
--
-- Theorem 1.1 uses three modular-function differences:
--
--   Fricke prime level : v_p(J_1 - J_{p+})
--   prime level        : v_p(J_1 - J_p)
--   prime-square level : v_p(J_1 - J_{p^2})
--
-- Duncan--Swisher's formulas (1.8)--(1.10), evaluated at p=2,3, give:
--
--   p=2 : 12 + 16 + 8 = 36
--   p=3 :  6 +  9 + 3 = 18
--
-- This module records that exact termwise baseline so any future wild
-- correction must say WHICH of the three modular valuations receives each
-- local contribution.  A total +10/+2 payment alone is not enough.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; _+_)

import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Moonshine.MonsterOrderExponentCorrectionExact as Exponent
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

data SmallPrime : Set where
  pTwo pThree : SmallPrime

data HauptmodulTerm : Set where
  frickePrimeLevel :
    HauptmodulTerm
  primeLevel :
    HauptmodulTerm
  primeSquareLevel :
    HauptmodulTerm

baselineValuation :
  SmallPrime ->
  HauptmodulTerm ->
  Nat

baselineValuation pTwo frickePrimeLevel = 12
baselineValuation pTwo primeLevel = 16
baselineValuation pTwo primeSquareLevel = 8

baselineValuation pThree frickePrimeLevel = 6
baselineValuation pThree primeLevel = 9
baselineValuation pThree primeSquareLevel = 3

baselineTotal :
  SmallPrime ->
  Nat
baselineTotal prime =
  baselineValuation prime frickePrimeLevel
  + baselineValuation prime primeLevel
  + baselineValuation prime primeSquareLevel

p2FrickePrimeBaselineIsTwelve :
  baselineValuation pTwo frickePrimeLevel ≡ 12
p2FrickePrimeBaselineIsTwelve = refl

p2PrimeBaselineIsSixteen :
  baselineValuation pTwo primeLevel ≡ 16
p2PrimeBaselineIsSixteen = refl

p2PrimeSquareBaselineIsEight :
  baselineValuation pTwo primeSquareLevel ≡ 8
p2PrimeSquareBaselineIsEight = refl

p3FrickePrimeBaselineIsSix :
  baselineValuation pThree frickePrimeLevel ≡ 6
p3FrickePrimeBaselineIsSix = refl

p3PrimeBaselineIsNine :
  baselineValuation pThree primeLevel ≡ 9
p3PrimeBaselineIsNine = refl

p3PrimeSquareBaselineIsThree :
  baselineValuation pThree primeSquareLevel ≡ 3
p3PrimeSquareBaselineIsThree = refl

p2BaselineTotalIsThirtySix :
  baselineTotal pTwo ≡ 36
p2BaselineTotalIsThirtySix = refl

p3BaselineTotalIsEighteen :
  baselineTotal pThree ≡ 18
p3BaselineTotalIsEighteen = refl

p2BaselineMatchesDuncanSwisherExceptionalRHS :
  baselineTotal pTwo
  ≡ Exponent.duncanSwisherExceptionalRHS Lane.p2
p2BaselineMatchesDuncanSwisherExceptionalRHS = refl

p3BaselineMatchesDuncanSwisherExceptionalRHS :
  baselineTotal pThree
  ≡ Exponent.duncanSwisherExceptionalRHS Lane.p3
p3BaselineMatchesDuncanSwisherExceptionalRHS = refl

------------------------------------------------------------------------
-- Termwise correction interface.
------------------------------------------------------------------------

record SmallPrimeTermwiseCorrection : Set₁ where
  field
    p2CorrectionAt :
      HauptmodulTerm -> Nat

    p3CorrectionAt :
      HauptmodulTerm -> Nat

    p2CorrectionTotal :
      p2CorrectionAt frickePrimeLevel
      + p2CorrectionAt primeLevel
      + p2CorrectionAt primeSquareLevel
      ≡ 10

    p3CorrectionTotal :
      p3CorrectionAt frickePrimeLevel
      + p3CorrectionAt primeLevel
      + p3CorrectionAt primeSquareLevel
      ≡ 2

    p2CorrectedTermSumPaysMonsterExponent :
      Exponent.monsterOrderExponent Lane.p2
      ≡
      (baselineValuation pTwo frickePrimeLevel
        + p2CorrectionAt frickePrimeLevel)
      +
      (baselineValuation pTwo primeLevel
        + p2CorrectionAt primeLevel)
      +
      (baselineValuation pTwo primeSquareLevel
        + p2CorrectionAt primeSquareLevel)

    p3CorrectedTermSumPaysMonsterExponent :
      Exponent.monsterOrderExponent Lane.p3
      ≡
      (baselineValuation pThree frickePrimeLevel
        + p3CorrectionAt frickePrimeLevel)
      +
      (baselineValuation pThree primeLevel
        + p3CorrectionAt primeLevel)
      +
      (baselineValuation pThree primeSquareLevel
        + p3CorrectionAt primeSquareLevel)

------------------------------------------------------------------------
-- No preferred distribution is invented.
------------------------------------------------------------------------

data TotalGapDeterminesTermwiseDistribution : Set where
data SectorRankDeterminesTermwiseDistribution : Set where
data WildDifferentDeterminesTermwiseDistribution : Set where

totalGapDoesNotDetermineTermwiseDistribution :
  TotalGapDeterminesTermwiseDistribution -> ⊥
totalGapDoesNotDetermineTermwiseDistribution ()

sectorRankDoesNotDetermineTermwiseDistribution :
  SectorRankDeterminesTermwiseDistribution -> ⊥
sectorRankDoesNotDetermineTermwiseDistribution ()

wildDifferentDoesNotDetermineTermwiseDistribution :
  WildDifferentDeterminesTermwiseDistribution -> ⊥
wildDifferentDoesNotDetermineTermwiseDistribution ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryFormalReconstruction

record HauptmodulTermBaselineBoundary : Set where
  constructor hauptmodul-term-baseline-boundary
  field
    p2ThreeTermBaselineTwelveSixteenEight : Bool
    p3ThreeTermBaselineSixNineThree : Bool
    p2BaselineTotalThirtySix : Bool
    p3BaselineTotalEighteen : Bool
    termwiseCorrectionInterfaceOwned : Bool
    preferredTermwiseCorrectionDistributionKnown : Bool

canonicalHauptmodulTermBaselineBoundary :
  HauptmodulTermBaselineBoundary
canonicalHauptmodulTermBaselineBoundary =
  hauptmodul-term-baseline-boundary
    true true true true true false
