module DASHI.Education.DigitalESDSLRSourceReviewBridgeRegression where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDSLRSourceReviewBridgeExact as Bridge

metadataCannotEnterSLRSecondStage :
  Bridge.MetadataOnlyCandidateEntersSLRSecondStage → ⊥
metadataCannotEnterSLRSecondStage =
  Bridge.metadataOnlyCandidateDoesNotEnterSLRSecondStage

slrExtractionCannotCreateAuditAdmission :
  Bridge.SLRExtractionCreatesSourceAuditAdmission → ⊥
slrExtractionCannotCreateAuditAdmission =
  Bridge.slrExtractionDoesNotCreateSourceAuditAdmission

slrClaimCandidateCannotCreatePaperTruth :
  Bridge.SLRClaimCandidateCreatesPaperTruth → ⊥
slrClaimCandidateCannotCreatePaperTruth =
  Bridge.slrClaimCandidateDoesNotCreatePaperTruth

reviewedObservationCannotCreateCompleteAudit :
  Bridge.ReviewedSLRObservationCreatesSourceAuditAdmission → ⊥
reviewedObservationCannotCreateCompleteAudit =
  Bridge.reviewedSLRObservationDoesNotCreateSourceAuditAdmission

titleIdentityCannotReplaceSameObjectWeld :
  Bridge.TitleMatchCreatesSameObjectPaperIdentity → ⊥
titleIdentityCannotReplaceSameObjectWeld =
  Bridge.titleMatchDoesNotCreateSameObjectPaperIdentity


slrReviewPacketCannotCreateCorpusAuditedSource :
  Bridge.SLRReviewPacketCreatesCorpusAuditedSource → ⊥
slrReviewPacketCannotCreateCorpusAuditedSource =
  Bridge.slrReviewPacketDoesNotCreateCorpusAuditedSource
