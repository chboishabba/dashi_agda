module DASHI.Moonshine.OggSSPP2FourARestrictedFingerprintOccurrenceNoGoExact where

------------------------------------------------------------------------
-- FIVE C4 FINGERPRINTS CANNOT ALL BE LABELS OF THE KNOWN 4A DECOMPOSITION
--
-- EXTERNAL:
-- Carnahan--Urano (IMRN 2024, Theorems 6.2 and 6.5) own the integral C4
-- indecomposable classification and actual 4A-supported labels A,D,C^A.
--
-- DASHI:
-- The five-candidate rank/trace witness family A,B,C,C^A,C^B is selected by
-- a separate repository predicate.  Actual 4A support cannot cover that
-- family, because B,C,C^B are absent.  This does not exclude their occurrence
-- in an independently constructed actual integral 2B source.  In particular,
-- no source is credited with a five-sector 2B localization theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Moonshine.OggSSPP2C4LowRankDepthSpectrumCandidateExact as Spectrum
import DASHI.Moonshine.OggSSPP2C4GreenFingerprintCandidateExact as Fingerprint
import DASHI.Moonshine.OggSSP4A2BTateRefinementFiveSectorNoGoExact as FourA
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Source-restricted support of the actual 4A indecomposable labels.
------------------------------------------------------------------------

data ActualFourAModule : Set where
  actualA actualD actualCA : ActualFourAModule

fourAModule :
  ActualFourAModule ->
  Spectrum.C4IntegralIndecomposable
fourAModule actualA = Spectrum.moduleA
fourAModule actualD = Spectrum.moduleD
fourAModule actualCA = Spectrum.moduleCA

actualFourAHasNoB :
  (m : ActualFourAModule) ->
  fourAModule m ≡ Spectrum.moduleB -> ⊥
actualFourAHasNoB actualA ()
actualFourAHasNoB actualD ()
actualFourAHasNoB actualCA ()

actualFourAHasNoC :
  (m : ActualFourAModule) ->
  fourAModule m ≡ Spectrum.moduleC -> ⊥
actualFourAHasNoC actualA ()
actualFourAHasNoC actualD ()
actualFourAHasNoC actualCA ()

actualFourAHasNoCB :
  (m : ActualFourAModule) ->
  fourAModule m ≡ Spectrum.moduleCB -> ⊥
actualFourAHasNoCB actualA ()
actualFourAHasNoCB actualD ()
actualFourAHasNoCB actualCA ()

------------------------------------------------------------------------
-- 2. Any all-five occurrence claim restricted to actual 4A support fails.
--    Notice the witness is required to preserve the original module label,
--    not simply match rank.  Rank alone loses A/B and C^A/C^B polarity.
------------------------------------------------------------------------

record FiveCandidatesFromActualFourA : Set where
  field
    assign :
      Spectrum.P2C4DepthCandidate ->
      ActualFourAModule

    correctOriginalLabel :
      (candidate : Spectrum.P2C4DepthCandidate) ->
      fourAModule (assign candidate)
      ≡
      Spectrum.candidateModule candidate

open FiveCandidatesFromActualFourA public

noFiveCandidatesFromActualFourA :
  FiveCandidatesFromActualFourA -> ⊥
noFiveCandidatesFromActualFourA attempt =
  actualFourAHasNoB
    (assign attempt Spectrum.candidateB)
    (correctOriginalLabel attempt Spectrum.candidateB)

------------------------------------------------------------------------
-- 3. Source-native fingerprints do not silently upgrade that support.
--    Even fingerprint preservation cannot place candidate B into the 4A
--    family: every actual 4A label has a distinct (rank,Tr(g)) value from B.
------------------------------------------------------------------------

actualFourARankTrace :
  ActualFourAModule ->
  Fingerprint.C4RankTraceFingerprint
actualFourARankTrace actualA =
  Fingerprint.rank-trace-fingerprint 1 Fingerprint.tracePlusOne
actualFourARankTrace actualD =
  Fingerprint.rank-trace-fingerprint 4 Fingerprint.traceZero
actualFourARankTrace actualCA =
  Fingerprint.rank-trace-fingerprint 3 Fingerprint.tracePlusOne

actualFourAFingerprintNotB :
  (m : ActualFourAModule) ->
  actualFourARankTrace m
  ≡ Fingerprint.candidateFingerprint Spectrum.candidateB ->
  ⊥
actualFourAFingerprintNotB actualA ()
actualFourAFingerprintNotB actualD ()
actualFourAFingerprintNotB actualCA ()

record FiveFingerprintsFromActualFourA : Set where
  field
    assign :
      Spectrum.P2C4DepthCandidate ->
      ActualFourAModule

    correctFingerprint :
      (candidate : Spectrum.P2C4DepthCandidate) ->
      actualFourARankTrace (assign candidate)
      ≡ Fingerprint.candidateFingerprint candidate

open FiveFingerprintsFromActualFourA public

noFiveFingerprintsFromActualFourA :
  FiveFingerprintsFromActualFourA -> ⊥
noFiveFingerprintsFromActualFourA attempt =
  actualFourAFingerprintNotB
    (assign attempt Spectrum.candidateB)
    (correctFingerprint attempt Spectrum.candidateB)

------------------------------------------------------------------------
-- 4. Authority boundary.
------------------------------------------------------------------------

fourATateSourceBoundary :
  FourA.FourA2BTateRefinementFiveSectorNoGoBoundary
fourATateSourceBoundary =
  FourA.canonicalFourA2BTateRefinementFiveSectorNoGoBoundary

data ActualFourAClassificationSettlesDirectTwoBOccurrence : Set where
data RankTraceInjectivityProvesIntegralTwoBMultiplicity : Set where
data FourANoGoDisprovesAllPossibleTwoBRealizations : Set where

fourADoesNotSettleTwoBOccurrence :
  ActualFourAClassificationSettlesDirectTwoBOccurrence -> ⊥
fourADoesNotSettleTwoBOccurrence ()

rankTraceDoesNotProveTwoBMultiplicity :
  RankTraceInjectivityProvesIntegralTwoBMultiplicity -> ⊥
rankTraceDoesNotProveTwoBMultiplicity ()

fourANoGoDoesNotEliminateIndependentTwoBSource :
  FourANoGoDisprovesAllPossibleTwoBRealizations -> ⊥
fourANoGoDoesNotEliminateIndependentTwoBSource ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryCrossModuleInference

record FourARestrictedFingerprintOccurrenceBoundary : Set where
  constructor four-a-restricted-fingerprint-occurrence-boundary
  field
    actualFourALabelSetSourceBacked : Bool
    fiveCandidateFamilyRepositorySelected : Bool
    labelsB_C_CBAbsentFromFourA : Bool
    sourceRankTraceFingerprintsCompared : Bool
    allFiveLabelRecognitionFromFourABlocked : Bool
    allFiveFingerprintRecognitionFromFourABlocked : Bool
    directTwoBOccurrenceDerived : Bool
    localizedDVRLengthDerived : Bool
    fourANoGoMisattributedToCarnahanUrano : Bool

canonicalFourARestrictedFingerprintOccurrenceBoundary :
  FourARestrictedFingerprintOccurrenceBoundary
canonicalFourARestrictedFingerprintOccurrenceBoundary =
  four-a-restricted-fingerprint-occurrence-boundary
    true true true true true true false false false
