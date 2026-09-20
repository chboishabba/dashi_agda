module DASHI.Interop.DigitalESD.ScholarlyFullTextInteropExecutionRegression where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Interop.DigitalESD.ScholarlyFullTextInteropExecutionExact as Exec

successfulProcessCannotCreateReview :
  Exec.SuccessfulParserProcessCreatesReviewPayment → ⊥
successfulProcessCannotCreateReview =
  Exec.successfulParserProcessDoesNotCreateReviewPayment

verifiedBundleCannotCreateAdmission :
  Exec.VerifiedParserBundleCreatesSourceAuditAdmission → ⊥
verifiedBundleCannotCreateAdmission =
  Exec.verifiedParserBundleDoesNotCreateSourceAuditAdmission

partialParseCannotPretendComplete :
  Exec.PartialParseCreatesCompleteCorpusReceipt → ⊥
partialParseCannotPretendComplete =
  Exec.partialParseDoesNotCreateCompleteCorpusReceipt
