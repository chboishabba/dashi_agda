module DASHI.Visualisation.CoarseSliceSearchExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- A finite ranking model for the attachment's float32/int8 failure mode.

data PlaneCandidate : Set where
  axisCandidate : PlaneCandidate
  broadAngledCandidate : PlaneCandidate
  compactIslandCandidate : PlaneCandidate

floatScore : PlaneCandidate → Nat
floatScore axisCandidate = 7
floatScore broadAngledCandidate = 10
floatScore compactIslandCandidate = 6

badQuantisedScore : PlaneCandidate → Nat
badQuantisedScore axisCandidate = 5
badQuantisedScore broadAngledCandidate = 4
badQuantisedScore compactIslandCandidate = 11

activeCoverage : PlaneCandidate → Nat
activeCoverage axisCandidate = 8
activeCoverage broadAngledCandidate = 9
activeCoverage compactIslandCandidate = 2

coverageAwareScore : PlaneCandidate → Nat
coverageAwareScore candidate =
  badQuantisedScore candidate + 2 * activeCoverage candidate

floatWinner : PlaneCandidate
floatWinner = broadAngledCandidate

badQuantisedWinner : PlaneCandidate
badQuantisedWinner = compactIslandCandidate

coverageAwareWinner : PlaneCandidate
coverageAwareWinner = broadAngledCandidate

floatWinnerScoreIsTen : floatScore floatWinner ≡ 10
floatWinnerScoreIsTen = refl

badWinnerDiffers : floatWinner ≡ badQuantisedWinner → ⊥
badWinnerDiffers ()

coverageRepairRestoresBroadWinner :
  coverageAwareScore coverageAwareWinner ≡ 22
coverageRepairRestoresBroadWinner = refl

compactCoverageAwareScoreIsFifteen :
  coverageAwareScore compactIslandCandidate ≡ 15
compactCoverageAwareScoreIsFifteen = refl

------------------------------------------------------------------------
-- Shortlist semantics: low precision proposes several candidates and the
-- exact objective reranks them.

data TwoCandidateShortlist : Set where
  broadAndCompact : TwoCandidateShortlist
  axisAndCompact : TwoCandidateShortlist

data InShortlist : PlaneCandidate → TwoCandidateShortlist → Set where
  broadIncluded :
    InShortlist broadAngledCandidate broadAndCompact
  compactIncludedWithBroad :
    InShortlist compactIslandCandidate broadAndCompact
  axisIncluded :
    InShortlist axisCandidate axisAndCompact
  compactIncludedWithAxis :
    InShortlist compactIslandCandidate axisAndCompact

coarseProposal : TwoCandidateShortlist
coarseProposal = broadAndCompact

trueWinnerSurvivesShortlist :
  InShortlist floatWinner coarseProposal
trueWinnerSurvivesShortlist = broadIncluded

floatRerankedWinner : TwoCandidateShortlist → PlaneCandidate
floatRerankedWinner broadAndCompact = broadAngledCandidate
floatRerankedWinner axisAndCompact = axisCandidate

shortlistRerankingRecoversWinner :
  floatRerankedWinner coarseProposal ≡ floatWinner
shortlistRerankingRecoversWinner = refl

------------------------------------------------------------------------
-- Safe low-precision data path metadata.

data StorageDType : Set where
  int8Storage : StorageDType
  float32Storage : StorageDType

data AccumulationDType : Set where
  int8Accumulation : AccumulationDType
  int32Accumulation : AccumulationDType
  float32Accumulation : AccumulationDType

record QuantisedPath : Set where
  constructor quantisedPath
  field
    storage : StorageDType
    accumulation : AccumulationDType

open QuantisedPath public

safeCoarsePath : QuantisedPath
safeCoarsePath = quantisedPath int8Storage int32Accumulation

unsafeWrappingPath : QuantisedPath
unsafeWrappingPath = quantisedPath int8Storage int8Accumulation

safeAndUnsafePathsDiffer :
  safeCoarsePath ≡ unsafeWrappingPath → ⊥
safeAndUnsafePathsDiffer ()

------------------------------------------------------------------------
-- Integer-scaled form of the round-to-nearest half-step bound.  Units are
-- doubled so no rational arithmetic is hidden.

quantisationStepDoubled : Nat
quantisationStepDoubled = 2

roundingErrorDoubled : Nat
roundingErrorDoubled = 1

halfStepBoundCloses :
  2 * roundingErrorDoubled ≡ quantisationStepDoubled
halfStepBoundCloses = refl

gridSamplingErrorDoubled : Nat
gridSamplingErrorDoubled = 3

combinedErrorBoundDoubled : Nat
combinedErrorBoundDoubled =
  roundingErrorDoubled + gridSamplingErrorDoubled

combinedErrorBoundIsFour :
  combinedErrorBoundDoubled ≡ 4
combinedErrorBoundIsFour = refl

record CoarseSliceSearchBoundary : Set where
  constructor coarseSliceSearchBoundary
  field
    oneInt8WinnerEstablishesRankingFidelity : Bool
    oneInt8WinnerEstablishesRankingFidelityIsFalse :
      oneInt8WinnerEstablishesRankingFidelity ≡ false

    conditionalActiveMeanAutomaticallyRewardsCoverage : Bool
    conditionalActiveMeanAutomaticallyRewardsCoverageIsFalse :
      conditionalActiveMeanAutomaticallyRewardsCoverage ≡ false

    twoOppositeCellCornersBoundNonlinearInterior : Bool
    twoOppositeCellCornersBoundNonlinearInteriorIsFalse :
      twoOppositeCellCornersBoundNonlinearInterior ≡ false

    int8StorageImpliesInt8Accumulation : Bool
    int8StorageImpliesInt8AccumulationIsFalse :
      int8StorageImpliesInt8Accumulation ≡ false

open CoarseSliceSearchBoundary public

canonicalCoarseSliceSearchBoundary : CoarseSliceSearchBoundary
canonicalCoarseSliceSearchBoundary =
  coarseSliceSearchBoundary
    false refl
    false refl
    false refl
    false refl
