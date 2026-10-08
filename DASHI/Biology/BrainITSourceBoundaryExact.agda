module DASHI.Biology.BrainITSourceBoundaryExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Source / attribution boundary for the Weizmann Brain-IT result.
--
-- Primary technical owners:
--   * Beliy et al., Brain-IT: Image Reconstruction from fMRI via
--     Brain-Interaction Transformer, arXiv:2510.25976, ICLR 2026.
--   * Beliy et al., The Wisdom of a Crowd of Brains: A Universal Brain
--     Encoder, arXiv:2406.12179.
--
-- Institutional exposition:
--   * Weizmann Institute of Science, 2026-09-14.
--
-- The uploaded transcript is represented only as a secondary social-media
-- paraphrase. It does not upgrade stronger extrapolations to paper claims.

data BrainITSource : Set where
  brainITArxiv251025976 : BrainITSource
  universalEncoderArxiv240612179 : BrainITSource
  weizmannInstitutionalRelease20260914 : BrainITSource
  uploadedTranscript20261008 : BrainITSource

data EvidenceRole : Set where
  primaryTechnical : EvidenceRole
  institutionalExposition : EvidenceRole
  secondaryParaphrase : EvidenceRole

sourceRole : BrainITSource → EvidenceRole
sourceRole brainITArxiv251025976 = primaryTechnical
sourceRole universalEncoderArxiv240612179 = primaryTechnical
sourceRole weizmannInstitutionalRelease20260914 = institutionalExposition
sourceRole uploadedTranscript20261008 = secondaryParaphrase

record BrainITSourceBoundary : Set where
  constructor brainITSourceBoundary
  field
    viewedImageReconstructionFromFMRI : Bool
    viewedImageReconstructionFromFMRIIsTrue :
      viewedImageReconstructionFromFMRI ≡ true

    functionalClustersSharedAcrossSubjects : Bool
    functionalClustersSharedAcrossSubjectsIsTrue :
      functionalClustersSharedAcrossSubjects ≡ true

    reportedClusterCountIs128 : Bool
    reportedClusterCountIs128IsTrue :
      reportedClusterCountIs128 ≡ true

    oneHourTransferComparableToFullFortyHourBaseline : Bool
    oneHourTransferComparableToFullFortyHourBaselineIsTrue :
      oneHourTransferComparableToFullFortyHourBaseline ≡ true

    fifteenMinuteRecognisableImageIsPrimaryPaperClaim : Bool
    fifteenMinuteRecognisableImageIsPrimaryPaperClaimIsFalse :
      fifteenMinuteRecognisableImageIsPrimaryPaperClaim ≡ false

    arbitraryThoughtReadingSupported : Bool
    arbitraryThoughtReadingSupportedIsFalse :
      arbitraryThoughtReadingSupported ≡ false

    remotePointAtPersonReadingSupported : Bool
    remotePointAtPersonReadingSupportedIsFalse :
      remotePointAtPersonReadingSupported ≡ false

    dreamReadingEstablished : Bool
    dreamReadingEstablishedIsFalse :
      dreamReadingEstablished ≡ false

canonicalBrainITSourceBoundary : BrainITSourceBoundary
canonicalBrainITSourceBoundary =
  brainITSourceBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
