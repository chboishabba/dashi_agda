module DASHI.Physics.Foundations.CabarlahEvidenceWitnessExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.CabarlahClaimStatusExact as Claims

------------------------------------------------------------------------
-- Positive evidence is indexed by the exact claim it supports.  There are no
-- constructors for refuted or underdetermined claims, so a status label alone
-- cannot be mistaken for a witness.

data EvidenceWitness : Claims.CabarlahClaim → Set where
  conventionalSpellingWitness :
    EvidenceWitness Claims.cabarlahConventionalEnglishSpelling

  coordinateCalculationWitness :
    EvidenceWitness Claims.cabarlahNearBrisbaneLatitude

  postwarSignalsRecordWitness :
    EvidenceWitness Claims.postwarCabarlahSignalsIntelligence

  pineGapDemandPairWitness :
    EvidenceWitness Claims.pineGapProtestJoinedLandReturnAndPalestine

noHistoricalCapbarlahWitness :
  EvidenceWitness Claims.capbarlahHistoricalSpelling → ⊥
noHistoricalCapbarlahWitness ()

noUniqueSourcePronunciationWitness :
  EvidenceWitness Claims.exactIndigenousSourcePronunciation → ⊥
noUniqueSourcePronunciationWitness ()

noFixedOfficialBrisbaneLineWitness :
  EvidenceWitness Claims.officialFixedBrisbaneSurrenderLine → ⊥
noFixedOfficialBrisbaneLineWitness ()

noCommunistConcessionBoundaryWitness :
  EvidenceWitness Claims.communistConcessionBoundaryAtCabarlah → ⊥
noCommunistConcessionBoundaryWitness ()

------------------------------------------------------------------------
-- A compact bundle of the four positively supported claims.  The bundle has no
-- field from which a refuted claim can be projected.

record SupportedCabarlahEvidence : Set where
  constructor supportedCabarlahEvidence
  field
    conventionalSpelling :
      EvidenceWitness Claims.cabarlahConventionalEnglishSpelling

    coordinateCalculation :
      EvidenceWitness Claims.cabarlahNearBrisbaneLatitude

    postwarSignalsRecord :
      EvidenceWitness Claims.postwarCabarlahSignalsIntelligence

    pineGapDemandPair :
      EvidenceWitness Claims.pineGapProtestJoinedLandReturnAndPalestine

open SupportedCabarlahEvidence public

canonicalSupportedCabarlahEvidence : SupportedCabarlahEvidence
canonicalSupportedCabarlahEvidence =
  supportedCabarlahEvidence
    conventionalSpellingWitness
    coordinateCalculationWitness
    postwarSignalsRecordWitness
    pineGapDemandPairWitness

------------------------------------------------------------------------
-- A disputed narrative can be recorded without constructing a fact witness.

data DiscussionStatus : Set where
  allegationRecorded : DiscussionStatus
  historicalDisputeRecorded : DiscussionStatus

record DiscussedWithoutFactWitness : Set where
  constructor discussedWithoutFactWitness
  field
    claim : Claims.CabarlahClaim
    discussion : DiscussionStatus
    factWitnessAbsent : EvidenceWitness claim → ⊥

open DiscussedWithoutFactWitness public

brisbaneLineDiscussion : DiscussedWithoutFactWitness
brisbaneLineDiscussion =
  discussedWithoutFactWitness
    Claims.officialFixedBrisbaneSurrenderLine
    historicalDisputeRecorded
    noFixedOfficialBrisbaneLineWitness

communistBoundaryCorrection : DiscussedWithoutFactWitness
communistBoundaryCorrection =
  discussedWithoutFactWitness
    Claims.communistConcessionBoundaryAtCabarlah
    allegationRecorded
    noCommunistConcessionBoundaryWitness

record EvidenceWitnessBoundary : Set where
  constructor evidenceWitnessBoundary
  field
    statusLabelCreatesFactWitness : Bool
    statusLabelCreatesFactWitnessIsFalse :
      statusLabelCreatesFactWitness ≡ false

    discussionCreatesHistoricalFact : Bool
    discussionCreatesHistoricalFactIsFalse :
      discussionCreatesHistoricalFact ≡ false

    supportedBundleContainsRefutedClaim : Bool
    supportedBundleContainsRefutedClaimIsFalse :
      supportedBundleContainsRefutedClaim ≡ false

open EvidenceWitnessBoundary public

canonicalEvidenceWitnessBoundary : EvidenceWitnessBoundary
canonicalEvidenceWitnessBoundary =
  evidenceWitnessBoundary
    false refl
    false refl
    false refl
