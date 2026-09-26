module DASHI.Moonshine.OggSSPSmallCharacteristicHauptmodulDivisorCutsetExact where

------------------------------------------------------------------------
-- MINIMAL HAUPTMODUL-DIVISOR CUTSET FOR p=2,3
--
-- Sufficient analytic theorem
-- ---------------------------
-- Let C_p denote the corrected small-prime modular-function object whose
-- valuation is meant to repair the Duncan--Swisher continuation.
--
-- It is enough to prove:
--
--   (1) C_p has one local valuation unit on each canonical invariant sector;
--   (2) the global exceptional correction is the sum of those local orders.
--
-- For the canonical sector bases this forces:
--
--   p=2 : 10 local units,
--   p=3 :  2 local units.
--
-- This is substantially narrower than reproving all of Dwork's p-adic cycle
-- theory or all of wild-stack modular-form theory.
--
-- Nothing in this module asserts that such a divisor theorem is already known.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.OggSSPSmallCharacteristicCorrectedValuationPaymentExact as Payment
import DASHI.Moonshine.OggSSPSmallCharacteristicInvariantClassRankExact as Rank
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Canonical candidate.
------------------------------------------------------------------------

candidate :
  Payment.CandidateSmallPrimeCorrectionPayment
candidate =
  Payment.canonicalCandidateSmallPrimeCorrectionPayment

------------------------------------------------------------------------
-- 2. Minimal local-divisor authority.
------------------------------------------------------------------------

record SmallPrimeCorrectedHauptmodulDivisorAuthority : Set₁ where
  field
    CorrectedDivisorLocalTerm : Set

    p2DivisorTerm :
      Payment.P2Sector candidate ->
      CorrectedDivisorLocalTerm

    p3DivisorTerm :
      Payment.P3Sector candidate ->
      CorrectedDivisorLocalTerm

    localOrder :
      CorrectedDivisorLocalTerm ->
      Nat

    p2EachSectorHasSimpleOrder :
      (sector : Payment.P2Sector candidate) ->
      localOrder (p2DivisorTerm sector) ≡ 1

    p3EachSectorHasSimpleOrder :
      (sector : Payment.P3Sector candidate) ->
      localOrder (p3DivisorTerm sector) ≡ 1

    p2GlobalCorrectionIsLocalOrderSum : Bool
    p2GlobalCorrectionIsLocalOrderSumIsTrue :
      p2GlobalCorrectionIsLocalOrderSum ≡ true

    p3GlobalCorrectionIsLocalOrderSum : Bool
    p3GlobalCorrectionIsLocalOrderSumIsTrue :
      p3GlobalCorrectionIsLocalOrderSum ≡ true

    divisorComesFromCorrectedHauptmodulDifference : Bool
    divisorComesFromCorrectedHauptmodulDifferenceIsTrue :
      divisorComesFromCorrectedHauptmodulDifference ≡ true

open SmallPrimeCorrectedHauptmodulDivisorAuthority public

------------------------------------------------------------------------
-- 3. Adapter into the route-neutral corrected valuation interface.
------------------------------------------------------------------------

asCorrectedValuationAuthority :
  SmallPrimeCorrectedHauptmodulDivisorAuthority ->
  Payment.SmallPrimeCorrectedValuationAuthority candidate
asCorrectedValuationAuthority authority =
  record
    { Payment.CorrectedLocalValuationTerm =
        CorrectedDivisorLocalTerm authority
    ; Payment.p2AnalyticLocalTerm =
        p2DivisorTerm authority
    ; Payment.p3AnalyticLocalTerm =
        p3DivisorTerm authority
    ; Payment.valuationMultiplicity =
        localOrder authority
    ; Payment.p2CandidateContributionIsAnalytic =
        λ sector ->
          sym (p2EachSectorHasSimpleOrder authority sector)
    ; Payment.p3CandidateContributionIsAnalytic =
        λ sector ->
          sym (p3EachSectorHasSimpleOrder authority sector)
    ; Payment.analyticRoute =
        Payment.directCorrectedHauptmodulValuation
    ; Payment.correctedQExpansionValuationTheorem =
        true
    ; Payment.correctedQExpansionValuationTheoremIsTrue =
        refl
    ; Payment.localTermsAssembleToHauptmodulDifferenceValuation =
        true
    ; Payment.localTermsAssembleToHauptmodulDifferenceValuationIsTrue =
        refl
    }

------------------------------------------------------------------------
-- 4. Why simple local order is exactly the invariant-basis rank candidate.
------------------------------------------------------------------------

p2ExpectedLocalOrderSum :
  Payment.p2CandidateWildCorrection
  ≡ Rank.listRank Rank.p2OrientedInvariantBasis
p2ExpectedLocalOrderSum =
  Payment.p2CandidateCorrectionIsInvariantFunctionRank

p3ExpectedLocalOrderSum :
  Payment.p3CandidateWildCorrection
  ≡ Rank.listRank Rank.p3InvariantStratumBasis
p3ExpectedLocalOrderSum =
  Payment.p3CandidateCorrectionIsInvariantFunctionRank

------------------------------------------------------------------------
-- 5. No fake authority.
------------------------------------------------------------------------

data RankOnePerBasisProvesDivisorTheorem : Set where
data WildStackinessAloneProvesDivisorTheorem : Set where
data RawDifferentCoefficientProvesDivisorTheorem : Set where

rankOnePerBasisDoesNotProveDivisorTheorem :
  RankOnePerBasisProvesDivisorTheorem -> ⊥
rankOnePerBasisDoesNotProveDivisorTheorem ()

wildStackinessAloneDoesNotProveDivisorTheorem :
  WildStackinessAloneProvesDivisorTheorem -> ⊥
wildStackinessAloneDoesNotProveDivisorTheorem ()

rawDifferentCoefficientDoesNotProveDivisorTheorem :
  RawDifferentCoefficientProvesDivisorTheorem -> ⊥
rawDifferentCoefficientDoesNotProveDivisorTheorem ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record HauptmodulDivisorCutsetBoundary : Set where
  constructor hauptmodul-divisor-cutset-boundary
  field
    canonicalP2SectorBasisFixed : Bool
    canonicalP3SectorBasisFixed : Bool
    sufficientSimpleLocalOrderTheoremSpecified : Bool
    sufficientGlobalSumTheoremSpecified : Bool
    adapterToCorrectedValuationAuthorityConstructed : Bool
    fullDworkReproofRequiredByCutset : Bool
    fullWildStackCohomologyRequiredByCutset : Bool
    divisorAuthorityCurrentlyInhabited : Bool
    invariantRankAlonePromotedToDivisorTheorem : Bool

canonicalHauptmodulDivisorCutsetBoundary :
  HauptmodulDivisorCutsetBoundary
canonicalHauptmodulDivisorCutsetBoundary =
  hauptmodul-divisor-cutset-boundary
    true true true true true false false false false
