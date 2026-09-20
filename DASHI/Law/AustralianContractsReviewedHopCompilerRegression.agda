module DASHI.Law.AustralianContractsReviewedHopCompilerRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Maybe using (just; nothing)

import DASHI.Law.AustralianContractsReviewedHopCompilerExact as Compiler
import DASHI.Law.SensibLawCitationUsePropositionExact as CitationUse
import DASHI.Law.AustralianContractsLegalFollowExact as Contracts

boundaryExists : Set
boundaryExists = Compiler.AustralianContractsReviewedHopCompilerBoundary

boundaryPaid : boundaryExists
boundaryPaid = Compiler.canonicalAustralianContractsReviewedHopCompilerBoundary

followedStillMapsToFollows :
  Compiler.citationUseTreatment CitationUse.followedUse
    ≡ just Contracts.follows
followedStillMapsToFollows = refl

mentionStillDoesNotMapToTreatment :
  Compiler.citationUseTreatment CitationUse.citedMention ≡ nothing
mentionStillDoesNotMapToTreatment = refl

rawOalcStillCannotAppendAuthority :
  Compiler.rawOalcReceiptMayAppendAuthorityNode
    Compiler.canonicalAustralianContractsReviewedHopCompilerBoundary
    ≡ false
rawOalcStillCannotAppendAuthority =
  Compiler.rawOalcReceiptMayAppendAuthorityNodeIsFalse
    Compiler.canonicalAustralianContractsReviewedHopCompilerBoundary

reviewedHopStillFeedsAdaptiveDelta :
  Compiler.reviewedHopFeedsExistingAdaptiveDelta
    Compiler.canonicalAustralianContractsReviewedHopCompilerBoundary
    ≡ true
reviewedHopStillFeedsAdaptiveDelta =
  Compiler.reviewedHopFeedsExistingAdaptiveDeltaIsTrue
    Compiler.canonicalAustralianContractsReviewedHopCompilerBoundary


reviewedAliasMayResolveTreatmentIdentity :
  Compiler.reviewedDocumentAliasMayResolveTreatmentIdentity
    Compiler.canonicalAustralianContractsReviewedHopCompilerBoundary
    ≡ true
reviewedAliasMayResolveTreatmentIdentity =
  Compiler.reviewedDocumentAliasMayResolveTreatmentIdentityIsTrue
    Compiler.canonicalAustralianContractsReviewedHopCompilerBoundary

rawOalcDocumentStillDoesNotCreateAlias :
  Compiler.rawOalcDocumentCreatesCanonicalAlias
    Compiler.canonicalAustralianContractsReviewedHopCompilerBoundary
    ≡ false
rawOalcDocumentStillDoesNotCreateAlias =
  Compiler.rawOalcDocumentCreatesCanonicalAliasIsFalse
    Compiler.canonicalAustralianContractsReviewedHopCompilerBoundary

reviewedAliasStillDoesNotRewriteSourceIdentity :
  Compiler.reviewedAliasRewritesSourceDocumentIdentity
    Compiler.canonicalAustralianContractsReviewedHopCompilerBoundary
    ≡ false
reviewedAliasStillDoesNotRewriteSourceIdentity =
  Compiler.reviewedAliasRewritesSourceDocumentIdentityIsFalse
    Compiler.canonicalAustralianContractsReviewedHopCompilerBoundary


rejectedIdentityStillCannotCreateAlias :
  Compiler.rejectedIdentityReviewMayCreateDocumentAlias
    Compiler.canonicalAustralianContractsReviewedHopCompilerBoundary
    ≡ false
rejectedIdentityStillCannotCreateAlias =
  Compiler.rejectedIdentityReviewMayCreateDocumentAliasIsFalse
    Compiler.canonicalAustralianContractsReviewedHopCompilerBoundary

reviewedAliasStillBindsExactOalcVersion :
  Compiler.reviewedAliasBindsExactOalcVersion
    Compiler.canonicalAustralianContractsReviewedHopCompilerBoundary
    ≡ true
reviewedAliasStillBindsExactOalcVersion =
  Compiler.reviewedAliasBindsExactOalcVersionIsTrue
    Compiler.canonicalAustralianContractsReviewedHopCompilerBoundary
