module DASHI.Moonshine.OggSSP2B3BPadicAnnihilationSlopeComparisonExact where

------------------------------------------------------------------------
-- 2B / 3B p-ADIC ANNIHILATION-SLOPE COMPARISON
--
-- EXTERNAL COMPUTATIONAL SOURCE
--
-- Chen--Marks--Tyler, Appendix A, "Table of annihilation", defines notation
--
--   a_1,...,a_m -> b_1,...,b_n
--
-- so that the valuation sequence starts with a_1,...,a_m and every later
-- term is obtained by adding b_{k mod n}.  Their table records:
--
--   2B at p=2 : 11 -> 3
--   3B at p=3 :  5 -> 2.
--
-- Hence the numerically observed eventual increments are:
--
--   slope_2B,2 = 3
--   slope_3B,3 = 2.
--
-- EVIDENCE GRADE
--
-- Appendix A explicitly describes these as the precise congruences that
-- "numerically appear".  DASHI therefore records the table entries as sourced
-- computational evidence, NOT as a theorem proved by Chen--Marks--Tyler.
--
-- CROSS-MODULE COMPARISON
--
-- Independent Monster-local residuals are:
--
--   R_2 = 10
--   R_3 =  2.
--
-- Therefore:
--
--   slope_2B,2 = 3 != 10,
--   slope_3B,3 = 2  =  2.
--
-- This gives a p=3 source-native analytic observable with the correct number,
-- while simultaneously ruling out one uniform "p-adic slope = residual" law.
-- It does NOT prove that the 3B slope is the Duncan--Swisher fourth term.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Moonshine.OggSSPSmallPrimeMonsterLocalCentralizerValuationExact as Local
import DASHI.Moonshine.OggSSP2B3BFirstUpCoefficientNoGoExact as FirstUp
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Source attribution and evidence grade.
------------------------------------------------------------------------

chenMarksTyler : Source.AttributedSource
chenMarksTyler =
  Source.mkDOISource
    "Ryan C. Chen, Samuel Marks, and Matthew Tyler"
    "p-adic Properties of Hauptmoduln with Applications to Moonshine"
    "SIGMA 15 (2019), 033"
    "2019"
    "10.3842/SIGMA.2019.033"
    "https://doi.org/10.3842/SIGMA.2019.033"
    Source.academicArticleSource
    "Appendix A defines the annihilation-sequence notation and tabulates the numerically observed entries 2B@2 = 11 -> 3 and 3B@3 = 5 -> 2. These table patterns are recorded as sourced computational evidence, not promoted to a proved theorem"
    Source.publicAttribution

padicSlopeSourceAtlas : Source.AttributedSourceAtlas
padicSlopeSourceAtlas =
  Source.mkSourceAtlas
    "2B/3B p-adic annihilation-slope comparison"
    "DASHI.Moonshine.OggSSP2B3BPadicAnnihilationSlopeComparisonExact"
    (chenMarksTyler ∷ [])
    "Chen--Marks--Tyler own the Appendix A numerical annihilation table and its notation; DASHI owns the comparison of the observed increments with the independently defined 10/2 Monster-local residuals"

data CMTAppendixEvidenceGrade : Set where
  sourcedNumericalPattern :
    CMTAppendixEvidenceGrade
  provedCMTTheorem :
    CMTAppendixEvidenceGrade

annihilationTableEvidenceGrade :
  CMTAppendixEvidenceGrade
annihilationTableEvidenceGrade =
  sourcedNumericalPattern

data CMTAppendixPatternIsPublishedProof : Set where

appendixPatternNotPromotedToPublishedProof :
  CMTAppendixPatternIsPublishedProof -> ⊥
appendixPatternNotPromotedToPublishedProof ()

------------------------------------------------------------------------
-- 2. Exact finite representation of the two observed arithmetic progressions.
------------------------------------------------------------------------

data SmallPrimeClass : Set where
  class2BAt2 :
    SmallPrimeClass
  class3BAt3 :
    SmallPrimeClass

initialValuation :
  SmallPrimeClass ->
  Nat
initialValuation class2BAt2 = 11
initialValuation class3BAt3 = 5

eventualIncrement :
  SmallPrimeClass ->
  Nat
eventualIncrement class2BAt2 = 3
eventualIncrement class3BAt3 = 2

valuationAtStep :
  SmallPrimeClass ->
  Nat ->
  Nat
valuationAtStep class 0 =
  initialValuation class
valuationAtStep class (suc n) =
  valuationAtStep class n + eventualIncrement class

p2FirstObservedValuationIsEleven :
  initialValuation class2BAt2 ≡ 11
p2FirstObservedValuationIsEleven = refl

p3FirstObservedValuationIsFive :
  initialValuation class3BAt3 ≡ 5
p3FirstObservedValuationIsFive = refl

p2ObservedIncrementIsThree :
  eventualIncrement class2BAt2 ≡ 3
p2ObservedIncrementIsThree = refl

p3ObservedIncrementIsTwo :
  eventualIncrement class3BAt3 ≡ 2
p3ObservedIncrementIsTwo = refl

------------------------------------------------------------------------
-- 3. Reconcile with the existing one-step no-go.
------------------------------------------------------------------------

p2InitialMatchesFirstUpValuation :
  initialValuation class2BAt2
  ≡ FirstUp.p2FirstUpValuation
p2InitialMatchesFirstUpValuation = refl

p3InitialMatchesFirstUpValuation :
  initialValuation class3BAt3
  ≡ FirstUp.p3FirstUpValuation
p3InitialMatchesFirstUpValuation = refl

------------------------------------------------------------------------
-- 4. Compare the sourced numerical slopes with Monster-local residuals.
------------------------------------------------------------------------

p2ObservedIncrementDoesNotMatchLocalResidual :
  eventualIncrement class2BAt2
  ≡ Local.p2LocalCentralizerResidual
  ->
  ⊥
p2ObservedIncrementDoesNotMatchLocalResidual ()

p3ObservedIncrementMatchesLocalResidual :
  eventualIncrement class3BAt3
  ≡ Local.p3LocalCentralizerResidual
p3ObservedIncrementMatchesLocalResidual = refl

data UniformPadicSlopeResidualLaw : Set where

uniformPadicSlopeResidualLawRejected :
  UniformPadicSlopeResidualLaw -> ⊥
uniformPadicSlopeResidualLawRejected ()

------------------------------------------------------------------------
-- 5. The p=3 match is a new analytic clue, not the missing same-object theorem.
------------------------------------------------------------------------

data P3ObservedSlopeIsDuncanSwisherFourthTerm : Set where
data P3ObservedSlopeIdentifiesBadLevelExceptionalObject : Set where
data P3ObservedSlopeProvesMonsterCentralizerRecognition : Set where
data P2SlopeMayBeAdjustedToTenByTargetFitting : Set where

p3SlopeNotPromotedToFourthTerm :
  P3ObservedSlopeIsDuncanSwisherFourthTerm -> ⊥
p3SlopeNotPromotedToFourthTerm ()

p3SlopeDoesNotIdentifyBadLevelExceptionalObject :
  P3ObservedSlopeIdentifiesBadLevelExceptionalObject -> ⊥
p3SlopeDoesNotIdentifyBadLevelExceptionalObject ()

p3SlopeDoesNotProveCentralizerRecognition :
  P3ObservedSlopeProvesMonsterCentralizerRecognition -> ⊥
p3SlopeDoesNotProveCentralizerRecognition ()

p2SlopeCannotBeTargetFittedToTen :
  P2SlopeMayBeAdjustedToTenByTargetFitting -> ⊥
p2SlopeCannotBeTargetFittedToTen ()

------------------------------------------------------------------------
-- 6. Prime-specific next theorem target.
------------------------------------------------------------------------

record P3PadicSlopeBadLevelRecognitionAuthority : Set₁ where
  field
    ExceptionalObject : Set

    p3Object :
      ExceptionalObject

    observedThreeBPadicSlope :
      ExceptionalObject ->
      Nat

    objectComesFromThreeBHauptmodulDynamics :
      Bool
    objectComesFromThreeBHauptmodulDynamicsIsTrue :
      objectComesFromThreeBHauptmodulDynamics ≡ true

    objectComesFromBadLevelSupersingularGeometry :
      Bool
    objectComesFromBadLevelSupersingularGeometryIsTrue :
      objectComesFromBadLevelSupersingularGeometry ≡ true

    slopeIsTwoFromSourceOrProof :
      observedThreeBPadicSlope p3Object ≡ 2

    slopeIsMonsterLocalResidual :
      observedThreeBPadicSlope p3Object
      ≡ Local.p3LocalCentralizerResidual

    proofIndependentOfTargetResidual :
      Bool
    proofIndependentOfTargetResidualIsTrue :
      proofIndependentOfTargetResidual ≡ true

open P3PadicSlopeBadLevelRecognitionAuthority public

data P3PadicSlopeBadLevelRecognitionAuthorityInhabited : Set where

p3PadicSlopeBadLevelRecognitionStillOpen :
  P3PadicSlopeBadLevelRecognitionAuthorityInhabited -> ⊥
p3PadicSlopeBadLevelRecognitionStillOpen ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record PadicAnnihilationSlopeComparisonBoundary : Set where
  constructor padic-annihilation-slope-comparison-boundary
  field
    cmtAppendixNotationSourced : Bool
    cmt2BAt2PatternElevenThenPlusThreeSourced : Bool
    cmt3BAt3PatternFiveThenPlusTwoSourced : Bool
    cmtAppendixPatternRecordedAsNumericalEvidence : Bool
    cmtAppendixPatternPromotedToTheorem : Bool
    p2ObservedSlopeThree : Bool
    p3ObservedSlopeTwo : Bool
    p2SlopeMatchesResidualTen : Bool
    p3SlopeMatchesResidualTwo : Bool
    uniformSlopeResidualLawSurvives : Bool
    p3SlopeBadLevelAuthoritySpecified : Bool
    p3SlopeBadLevelAuthorityInhabited : Bool
    attributionFirewallPreserved : Bool

canonicalPadicAnnihilationSlopeComparisonBoundary :
  PadicAnnihilationSlopeComparisonBoundary
canonicalPadicAnnihilationSlopeComparisonBoundary =
  padic-annihilation-slope-comparison-boundary
    true true true true false
    true true false true false
    true false true
