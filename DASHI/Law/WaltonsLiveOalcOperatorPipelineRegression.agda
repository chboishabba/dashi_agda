module DASHI.Law.WaltonsLiveOalcOperatorPipelineRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.WaltonsLiveOalcOperatorPipelineExact as Live

liveAcquisitionRemainsNativeRust :
  Live.liveOalcAcquisitionIsNativeRust Live.canonicalWaltonsLiveOalcPipelineBoundary
    ≡ true
liveAcquisitionRemainsNativeRust =
  Live.liveOalcAcquisitionIsNativeRustIsTrue Live.canonicalWaltonsLiveOalcPipelineBoundary

paragraphReviewRemainsHuman :
  Live.paragraphReviewIsAutomatic Live.canonicalWaltonsLiveOalcPipelineBoundary
    ≡ false
paragraphReviewRemainsHuman =
  Live.paragraphReviewIsAutomaticIsFalse Live.canonicalWaltonsLiveOalcPipelineBoundary

laterAuthoritiesRemainReacquiredViaOalc :
  Live.laterAuthoritiesAreReacquiredThroughOalc Live.canonicalWaltonsLiveOalcPipelineBoundary
    ≡ true
laterAuthoritiesRemainReacquiredViaOalc =
  Live.laterAuthoritiesAreReacquiredThroughOalcIsTrue
    Live.canonicalWaltonsLiveOalcPipelineBoundary

rawOalcIdentityStillDoesNotCreateAlias :
  Live.rawOalcIdentityCreatesCanonicalAlias Live.canonicalWaltonsLiveOalcPipelineBoundary
    ≡ false
rawOalcIdentityStillDoesNotCreateAlias =
  Live.rawOalcIdentityCreatesCanonicalAliasIsFalse
    Live.canonicalWaltonsLiveOalcPipelineBoundary

treatmentStillRequiresReview :
  Live.treatmentRequiresReview Live.canonicalWaltonsLiveOalcPipelineBoundary
    ≡ true
treatmentStillRequiresReview =
  Live.treatmentRequiresReviewIsTrue Live.canonicalWaltonsLiveOalcPipelineBoundary

livePipelineStillDoesNotCreateAuthority :
  Live.pipelineCreatesLegalAuthority Live.canonicalWaltonsLiveOalcPipelineBoundary
    ≡ false
livePipelineStillDoesNotCreateAuthority =
  Live.pipelineCreatesLegalAuthorityIsFalse Live.canonicalWaltonsLiveOalcPipelineBoundary
