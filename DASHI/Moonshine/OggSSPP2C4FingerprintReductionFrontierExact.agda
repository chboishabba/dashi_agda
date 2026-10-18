module DASHI.Moonshine.OggSSPP2C4FingerprintReductionFrontierExact where

------------------------------------------------------------------------
-- p=2 FINAL REDUCED SCALAR FRONTIER:
-- C4 SOURCE FINGERPRINT OCCURRENCE + LOCALIZED REDUCTION
--
-- PAID UPSTREAM
--
--  * source-compatible five-module C4 candidate family:
--      A, B, C, C^A, C^B;
--  * source ranks:
--      1,1,2,3,3;
--  * exact rechart to scalar slots:
--      1,1,2,3,3 <-> 3,3,2,1,1 ordering;
--  * injective source-native fingerprint:
--      (rank, Tr(g));
--  * p=3 reduced scalar authority:
--      representative H^0/H^1 simple factors have lengths 1,1.
--
-- UNPAID
--
--  OCCURRENCE:
--    actual integral 2B source pieces realize every one of the five candidate
--    C4 fingerprints (or a theorem-equivalent lift to them);
--
--  LOCALIZED REDUCTION:
--    the bad-level finite-length localization of those actual pieces is the
--    reduction/filtration whose normalized DVR length equals the integral rank.
--
-- Once both are paid, the reduced joint pB scalar authority is inhabited
-- without reading the Monster residual 10/2 or Base369 labels.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Moonshine.OggSSPP2C4GreenFingerprintCandidateExact as Fingerprint
import DASHI.Moonshine.OggSSPP2C4OccurrenceReductionCutsetExact as Cutset
import DASHI.Moonshine.OggSSPP2C4LowRankDepthSpectrumCandidateExact as Spectrum
import DASHI.Moonshine.OggSSPP2InertiaDepthQuotientExact as P2Scalar
import DASHI.Moonshine.OggSSPPBScalarLocalizationP2OnlyFrontierExact as Joint
import DASHI.Moonshine.OggSSPPBScalarLocalizationReductionExact as PB
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. A paid fingerprint occurrence theorem gives the occurrence half.
------------------------------------------------------------------------

asCandidateOccurrenceAuthority :
  Fingerprint.P2CandidateFingerprintOccurrenceAuthority ->
  Cutset.P2C4CandidateOccurrenceAuthority
asCandidateOccurrenceAuthority F =
  record
    { Cutset.SourcePiece =
        Fingerprint.SourcePiece F

    ; Cutset.sourcePiece =
        Fingerprint.sourcePiece F

    ; Cutset.comesFromActualIntegralTwoBTateObject =
        Fingerprint.sourcePieceComesFromActualIntegralTwoBTateObject F

    ; Cutset.comesFromActualIntegralTwoBTateObjectIsTrue =
        Fingerprint.sourcePieceComesFromActualIntegralTwoBTateObjectIsTrue F

    ; Cutset.candidateLabelOccurs =
        Fingerprint.everyCandidateActuallyOccurs F

    ; Cutset.candidateLabelOccursIsTrue =
        Fingerprint.everyCandidateActuallyOccursIsTrue F

    ; Cutset.occurrenceDerivedWithoutMonsterResidual =
        Fingerprint.occurrenceDerivedWithoutMonsterResidual F

    ; Cutset.occurrenceDerivedWithoutMonsterResidualIsTrue =
        Fingerprint.occurrenceDerivedWithoutMonsterResidualIsTrue F

    ; Cutset.occurrenceDerivedWithoutBase369 =
        Fingerprint.occurrenceDerivedWithoutBase369 F

    ; Cutset.occurrenceDerivedWithoutBase369IsTrue =
        Fingerprint.occurrenceDerivedWithoutBase369IsTrue F
    }

------------------------------------------------------------------------
-- 2. Both p=2 payments close the p=2 scalar source authority.
------------------------------------------------------------------------

p2ScalarAuthority :
  (F : Fingerprint.P2CandidateFingerprintOccurrenceAuthority) ->
  Cutset.P2C4LocalizedReductionAuthority
    (asCandidateOccurrenceAuthority F) ->
  P2Scalar.P2SourceDepthSlotLengthAuthority
p2ScalarAuthority F R =
  Cutset.asP2ScalarDepthAuthority
    (asCandidateOccurrenceAuthority F)
    R

p2ScalarTotalIsTen :
  (F : Fingerprint.P2CandidateFingerprintOccurrenceAuthority) ->
  (R :
    Cutset.P2C4LocalizedReductionAuthority
      (asCandidateOccurrenceAuthority F)) ->
  P2Scalar.sourceSlotTotal (p2ScalarAuthority F R) ≡ 10
p2ScalarTotalIsTen F R =
  P2Scalar.sourceSlotTotalIsTen
    (p2ScalarAuthority F R)

------------------------------------------------------------------------
-- 3. p=3 is already paid, so the same pair closes the joint reduced authority.
------------------------------------------------------------------------

jointScalarAuthority :
  (F : Fingerprint.P2CandidateFingerprintOccurrenceAuthority) ->
  Cutset.P2C4LocalizedReductionAuthority
    (asCandidateOccurrenceAuthority F) ->
  PB.PBScalarLocalizationAuthority
jointScalarAuthority F R =
  Joint.assembleFromP2
    (p2ScalarAuthority F R)

jointP2TotalIsTen :
  (F : Fingerprint.P2CandidateFingerprintOccurrenceAuthority) ->
  (R :
    Cutset.P2C4LocalizedReductionAuthority
      (asCandidateOccurrenceAuthority F)) ->
  PB.p2ScalarSourceTotal (jointScalarAuthority F R) ≡ 10
jointP2TotalIsTen F R =
  PB.p2ScalarSourceTotalIsTen
    (jointScalarAuthority F R)

jointP3TotalIsTwo :
  (F : Fingerprint.P2CandidateFingerprintOccurrenceAuthority) ->
  (R :
    Cutset.P2C4LocalizedReductionAuthority
      (asCandidateOccurrenceAuthority F)) ->
  PB.p3ScalarSourceTotal (jointScalarAuthority F R) ≡ 2
jointP3TotalIsTwo F R =
  PB.p3ScalarSourceTotalIsTwo
    (jointScalarAuthority F R)

------------------------------------------------------------------------
-- 4. The two payments are not interchangeable.
------------------------------------------------------------------------

data FingerprintInjectivityCreatesOccurrence : Set where
data OccurrenceCreatesLocalizedReduction : Set where
data LocalizedReductionCreatesOccurrence : Set where
data RankSpectrumAloneCreatesEitherPayment : Set where

fingerprintInjectivityDoesNotCreateOccurrence :
  FingerprintInjectivityCreatesOccurrence -> ⊥
fingerprintInjectivityDoesNotCreateOccurrence ()

occurrenceDoesNotCreateLocalizedReduction :
  OccurrenceCreatesLocalizedReduction -> ⊥
occurrenceDoesNotCreateLocalizedReduction ()

localizedReductionDoesNotCreateOccurrence :
  LocalizedReductionCreatesOccurrence -> ⊥
localizedReductionDoesNotCreateOccurrence ()

rankSpectrumAloneDoesNotCreatePayments :
  RankSpectrumAloneCreatesEitherPayment -> ⊥
rankSpectrumAloneDoesNotCreatePayments ()

------------------------------------------------------------------------
-- 5. Strong semantic / same-object localization remains separate.
------------------------------------------------------------------------

data ReducedScalarClosureCreatesFiveInertiaSectorRecognition : Set where
data ReducedScalarClosureCreatesIgusaHauptmodulLocalization : Set where
data ReducedScalarClosureCreatesMonsterSameObjectTheorem : Set where

reducedScalarDoesNotCreateFiveSectorRecognition :
  ReducedScalarClosureCreatesFiveInertiaSectorRecognition -> ⊥
reducedScalarDoesNotCreateFiveSectorRecognition ()

reducedScalarDoesNotCreateIgusaHauptmodulLocalization :
  ReducedScalarClosureCreatesIgusaHauptmodulLocalization -> ⊥
reducedScalarDoesNotCreateIgusaHauptmodulLocalization ()

reducedScalarDoesNotCreateMonsterSameObjectTheorem :
  ReducedScalarClosureCreatesMonsterSameObjectTheorem -> ⊥
reducedScalarDoesNotCreateMonsterSameObjectTheorem ()

------------------------------------------------------------------------
-- 6. Live state.
------------------------------------------------------------------------

data FingerprintOccurrencePaymentInhabited : Set where
data LocalizedReductionPaymentInhabited : Set where

fingerprintOccurrenceStillOpen :
  FingerprintOccurrencePaymentInhabited -> ⊥
fingerprintOccurrenceStillOpen ()

localizedReductionStillOpen :
  LocalizedReductionPaymentInhabited -> ⊥
localizedReductionStillOpen ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryNewExtension

record P2C4FingerprintReductionFrontierBoundary : Set where
  constructor p2-c4-fingerprint-reduction-frontier-boundary
  field
    sourceCompatibleFiveCandidateFamilyOwned : Bool
    sourceRankSpectrumThreeThreeTwoOneOneOwned : Bool
    rankTraceFingerprintInjective : Bool
    p3ReducedScalarPaymentAlreadyInhabited : Bool

    fingerprintOccurrencePaymentSpecified : Bool
    fingerprintOccurrencePaymentInhabited : Bool
    localizedReductionPaymentSpecified : Bool
    localizedReductionPaymentInhabited : Bool

    conditionalP2ScalarTotalTenDerived : Bool
    conditionalJointP3TotalTwoRetained : Bool

    fingerprintInjectivityPromotedToOccurrence : Bool
    occurrencePromotedToLocalizedReduction : Bool
    rankPromotedToLocalizedLengthWithoutRecognition : Bool

    fullFiveSectorSemanticLocalizationClaimed : Bool
    badLevelHauptmodulSameObjectClaimed : Bool

    monsterResidualUsedToDefinePayments : Bool
    base369UsedToDefinePayments : Bool
    attributionFirewallPreserved : Bool

canonicalP2C4FingerprintReductionFrontierBoundary :
  P2C4FingerprintReductionFrontierBoundary
canonicalP2C4FingerprintReductionFrontierBoundary =
  p2-c4-fingerprint-reduction-frontier-boundary
    true true true true
    true false true false
    true true
    false false false
    false false
    false false true
