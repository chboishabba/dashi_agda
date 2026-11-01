module DASHI.Moonshine.OggSSPP2C4OccurrenceReductionCutsetExact where

------------------------------------------------------------------------
-- p=2 C4 CANDIDATE OCCURRENCE / MOD-2 REDUCTION CUTSET
--
-- UPSTREAM
--
-- OggSSPP2C4LowRankDepthSpectrumCandidateExact supplies a source-native
-- five-module candidate family
--
--   A, B, C, C^A, C^B
--
-- with integral ranks
--
--   1,1,2,3,3
--
-- and an exact rechart to the scalar slots 3,3,2,1,1.
--
-- SOURCE ROLES
--
-- Carnahan--Urano own the integral C4 lattice classification/ranks and the
-- square-subgroup restriction table.
--
-- Urano owns the generalized-Brauer / arbitrary finite-length DVR framework.
--
-- DASHI owns this factorization of the remaining p=2 theorem into:
--
--   OCCURRENCE:
--     actual integral 2B source pieces realize the five candidate labels;
--
--   LOCAL REDUCTION:
--     the bad-level finite-length localization of each realized source piece
--     is identified with the mod-2 reduction/filtration whose normalized
--     composition length is the integral lattice rank.
--
-- Neither external source is credited with either identification unless it is
-- proved separately.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Moonshine.OggSSPP2C4LowRankDepthSpectrumCandidateExact as Spectrum
import DASHI.Moonshine.OggSSPP2InertiaDepthQuotientExact as Scalar
import DASHI.Moonshine.OggSSPSmallPrimeDVRLengthBrauerCutsetExact as DVR
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Algebraic reduction-length model.
--
-- For the finite abstraction used by this cutset, the normalized composition
-- length of the mod-2 reduction of a free rank-r integral lattice is r.
--
-- This is a DASHI algebraic model/normalization theorem.  It does NOT assert
-- that the actual p=2 bad-level localization is this reduction.
------------------------------------------------------------------------

modTwoReductionCompositionLength :
  Spectrum.P2C4DepthCandidate ->
  Nat
modTwoReductionCompositionLength candidate =
  Spectrum.candidateRank candidate

modTwoReductionLengthMatchesScalarSlot :
  (candidate : Spectrum.P2C4DepthCandidate) ->
  modTwoReductionCompositionLength candidate
  ≡
  Scalar.slotLength (Spectrum.candidateToScalarSlot candidate)
modTwoReductionLengthMatchesScalarSlot =
  Spectrum.candidateRankMatchesScalarSlotDepth

------------------------------------------------------------------------
-- 2. OCCURRENCE payment.
------------------------------------------------------------------------

record P2C4CandidateOccurrenceAuthority : Set₁ where
  field
    SourcePiece :
      Set

    sourcePiece :
      Spectrum.P2C4DepthCandidate ->
      SourcePiece

    comesFromActualIntegralTwoBTateObject :
      SourcePiece ->
      Bool

    comesFromActualIntegralTwoBTateObjectIsTrue :
      (piece : SourcePiece) ->
      comesFromActualIntegralTwoBTateObject piece ≡ true

    candidateLabelOccurs :
      Spectrum.P2C4DepthCandidate ->
      Bool

    candidateLabelOccursIsTrue :
      (candidate : Spectrum.P2C4DepthCandidate) ->
      candidateLabelOccurs candidate ≡ true

    occurrenceDerivedWithoutMonsterResidual :
      Bool

    occurrenceDerivedWithoutMonsterResidualIsTrue :
      occurrenceDerivedWithoutMonsterResidual ≡ true

    occurrenceDerivedWithoutBase369 :
      Bool

    occurrenceDerivedWithoutBase369IsTrue :
      occurrenceDerivedWithoutBase369 ≡ true

open P2C4CandidateOccurrenceAuthority public

------------------------------------------------------------------------
-- 3. LOCAL REDUCTION / LENGTH recognition payment.
------------------------------------------------------------------------

record P2C4LocalizedReductionAuthority
    (O : P2C4CandidateOccurrenceAuthority) : Set₁ where
  field
    normalizedLocalizedDVRLength :
      SourcePiece O ->
      Nat

    localizedPieceRecognisedAsModTwoReduction :
      Spectrum.P2C4DepthCandidate ->
      Bool

    localizedPieceRecognisedAsModTwoReductionIsTrue :
      (candidate : Spectrum.P2C4DepthCandidate) ->
      localizedPieceRecognisedAsModTwoReduction candidate ≡ true

    localizedLengthAgreesWithReductionLength :
      (candidate : Spectrum.P2C4DepthCandidate) ->
      normalizedLocalizedDVRLength
        (sourcePiece O candidate)
      ≡
      modTwoReductionCompositionLength candidate

    recognitionUsesUranoFiniteLengthDVRFramework :
      Bool

    recognitionUsesUranoFiniteLengthDVRFrameworkIsTrue :
      recognitionUsesUranoFiniteLengthDVRFramework ≡ true

    recognitionDerivedWithoutMonsterResidual :
      Bool

    recognitionDerivedWithoutMonsterResidualIsTrue :
      recognitionDerivedWithoutMonsterResidual ≡ true

    recognitionDerivedWithoutBase369 :
      Bool

    recognitionDerivedWithoutBase369IsTrue :
      recognitionDerivedWithoutBase369 ≡ true

open P2C4LocalizedReductionAuthority public

------------------------------------------------------------------------
-- 4. Composition closes the earlier rank->localized-length authority.
------------------------------------------------------------------------

assembleRankToLocalizedLength :
  (O : P2C4CandidateOccurrenceAuthority) ->
  P2C4LocalizedReductionAuthority O ->
  Spectrum.P2C4RankToLocalizedLengthAuthority
assembleRankToLocalizedLength O R =
  record
    { Spectrum.SourcePiece =
        SourcePiece O

    ; Spectrum.sourcePiece =
        sourcePiece O

    ; Spectrum.candidateLabelActuallyOccursInTwoBSource =
        candidateLabelOccurs O

    ; Spectrum.candidateLabelActuallyOccursInTwoBSourceIsTrue =
        candidateLabelOccursIsTrue O

    ; Spectrum.sourcePieceComesFromIntegralTwoBTateObject =
        comesFromActualIntegralTwoBTateObject O

    ; Spectrum.sourcePieceComesFromIntegralTwoBTateObjectIsTrue =
        comesFromActualIntegralTwoBTateObjectIsTrue O

    ; Spectrum.normalizedLocalizedDVRLength =
        normalizedLocalizedDVRLength R

    ; Spectrum.localizedLengthEqualsCandidateRank =
        localizedLengthAgreesWithReductionLength R

    ; Spectrum.recognitionIndependentOfMonsterResidualTen =
        recognitionDerivedWithoutMonsterResidual R

    ; Spectrum.recognitionIndependentOfMonsterResidualTenIsTrue =
        recognitionDerivedWithoutMonsterResidualIsTrue R

    ; Spectrum.recognitionIndependentOfBase369 =
        recognitionDerivedWithoutBase369 R

    ; Spectrum.recognitionIndependentOfBase369IsTrue =
        recognitionDerivedWithoutBase369IsTrue R
    }

asP2ScalarDepthAuthority :
  (O : P2C4CandidateOccurrenceAuthority) ->
  (R : P2C4LocalizedReductionAuthority O) ->
  Scalar.P2SourceDepthSlotLengthAuthority
asP2ScalarDepthAuthority O R =
  Spectrum.asP2SourceDepthSlotLengthAuthority
    (assembleRankToLocalizedLength O R)

assembledP2ScalarTotalIsTen :
  (O : P2C4CandidateOccurrenceAuthority) ->
  (R : P2C4LocalizedReductionAuthority O) ->
  Scalar.sourceSlotTotal (asP2ScalarDepthAuthority O R) ≡ 10
assembledP2ScalarTotalIsTen O R =
  Scalar.sourceSlotTotalIsTen
    (asP2ScalarDepthAuthority O R)

------------------------------------------------------------------------
-- 5. The two payments are logically independent.
------------------------------------------------------------------------

data ClassificationTableCreatesOccurrence : Set where
data OccurrenceCreatesLocalizedReductionRecognition : Set where
data RankCreatesBadLevelLocalization : Set where
data UranoDVRFrameworkCreatesSpecificLocalization : Set where

classificationTableDoesNotCreateOccurrence :
  ClassificationTableCreatesOccurrence -> ⊥
classificationTableDoesNotCreateOccurrence ()

occurrenceDoesNotCreateReductionRecognition :
  OccurrenceCreatesLocalizedReductionRecognition -> ⊥
occurrenceDoesNotCreateReductionRecognition ()

rankDoesNotCreateBadLevelLocalization :
  RankCreatesBadLevelLocalization -> ⊥
rankDoesNotCreateBadLevelLocalization ()

uranoFrameworkDoesNotCreateSpecificLocalization :
  UranoDVRFrameworkCreatesSpecificLocalization -> ⊥
uranoFrameworkDoesNotCreateSpecificLocalization ()

------------------------------------------------------------------------
-- 6. Source receipts.
------------------------------------------------------------------------

dvrBoundary :
  DVR.DVRLengthBrauerCutsetBoundary
dvrBoundary =
  DVR.canonicalDVRLengthBrauerCutsetBoundary

------------------------------------------------------------------------
-- 7. Live theorem wall.
------------------------------------------------------------------------

data P2C4CandidateOccurrenceAuthorityInhabited : Set where
data P2C4LocalizedReductionAuthorityInhabited : Set where

p2CandidateOccurrenceStillOpen :
  P2C4CandidateOccurrenceAuthorityInhabited -> ⊥
p2CandidateOccurrenceStillOpen ()

p2LocalizedReductionRecognitionStillOpen :
  P2C4LocalizedReductionAuthorityInhabited -> ⊥
p2LocalizedReductionRecognitionStillOpen ()

------------------------------------------------------------------------
-- 8. Attribution boundary.
------------------------------------------------------------------------

data CarnahanUranoCreditedWithCandidateOccurrence : Set where
data UranoCreditedWithSpecificModTwoLocalization : Set where
data ExternalSourceCreditedWithMonsterResidualTen : Set where

carnahanUranoNotCreditedWithCandidateOccurrence :
  CarnahanUranoCreditedWithCandidateOccurrence -> ⊥
carnahanUranoNotCreditedWithCandidateOccurrence ()

uranoNotCreditedWithSpecificLocalization :
  UranoCreditedWithSpecificModTwoLocalization -> ⊥
uranoNotCreditedWithSpecificModTwoLocalization ()

externalSourcesNotCreditedWithResidualTen :
  ExternalSourceCreditedWithMonsterResidualTen -> ⊥
externalSourcesNotCreditedWithResidualTen ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryNewExtension

record P2C4OccurrenceReductionCutsetBoundary : Set where
  constructor p2-c4-occurrence-reduction-cutset-boundary
  field
    fiveCandidateRankSpectrumOwned : Bool
    genericModTwoReductionLengthModelOwned : Bool
    occurrenceAuthoritySpecified : Bool
    occurrenceAuthorityInhabited : Bool
    localizedReductionAuthoritySpecified : Bool
    localizedReductionAuthorityInhabited : Bool
    assemblyToRankLengthAuthorityOwned : Bool
    assemblyToScalarDepthAuthorityOwned : Bool
    conditionalScalarTotalTenDerived : Bool
    occurrenceInferredFromClassificationAlone : Bool
    localizedReductionInferredFromRankAlone : Bool
    specificLocalizationAttributedToUrano : Bool
    occurrenceAttributedToCarnahanUrano : Bool
    monsterResidualUsedToDefinePayments : Bool
    base369UsedToDefinePayments : Bool
    attributionFirewallPreserved : Bool

canonicalP2C4OccurrenceReductionCutsetBoundary :
  P2C4OccurrenceReductionCutsetBoundary
canonicalP2C4OccurrenceReductionCutsetBoundary =
  p2-c4-occurrence-reduction-cutset-boundary
    true true true false true false true true true
    false false false false false false true
