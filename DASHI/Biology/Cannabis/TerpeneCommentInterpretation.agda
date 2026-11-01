module DASHI.Biology.Cannabis.TerpeneCommentInterpretation where

open import Agda.Builtin.Equality using (_≡_; refl)

-- The discussion contains several distinct claims.  They must not be merged
-- into one undifferentiated pro- or anti-terpene position.
data CommentClaim : Set where
  historical-taxonomy-claim : CommentClaim
  genomic-similarity-claim : CommentClaim
  label-predictiveness-critique : CommentClaim
  correlation-warning : CommentClaim
  terpene-causality-denial : CommentClaim
  medicinal-effect-question : CommentClaim

data SourceObligation : Set where
  historical-source-required : SourceObligation
  genomic-study-required : SourceObligation
  classification-study-required : SourceObligation
  methodological-guard-only : SourceObligation
  mechanistic-experiment-required : SourceObligation
  controlled-outcome-study-required : SourceObligation

obligation : CommentClaim → SourceObligation
obligation historical-taxonomy-claim      = historical-source-required
obligation genomic-similarity-claim       = genomic-study-required
obligation label-predictiveness-critique  = classification-study-required
obligation correlation-warning            = methodological-guard-only
obligation terpene-causality-denial        = mechanistic-experiment-required
obligation medicinal-effect-question      = controlled-outcome-study-required

data ClaimAuthority : Set where
  framing-only : ClaimAuthority
  source-bound-candidate : ClaimAuthority
  experiment-required : ClaimAuthority
  blocked-without-source : ClaimAuthority

authority : CommentClaim → ClaimAuthority
authority historical-taxonomy-claim      = source-bound-candidate
authority genomic-similarity-claim       = source-bound-candidate
authority label-predictiveness-critique  = source-bound-candidate
authority correlation-warning            = framing-only
authority terpene-causality-denial        = experiment-required
authority medicinal-effect-question      = experiment-required

correlation-warning-is-guard-not-proof :
  authority correlation-warning ≡ framing-only
correlation-warning-is-guard-not-proof = refl

genomic-comment-needs-genomic-source :
  obligation genomic-similarity-claim ≡ genomic-study-required
genomic-comment-needs-genomic-source = refl

causality-denial-is-itself-causal :
  obligation terpene-causality-denial ≡ mechanistic-experiment-required
causality-denial-is-itself-causal = refl

medicinal-question-needs-controlled-outcomes :
  obligation medicinal-effect-question ≡ controlled-outcome-study-required
medicinal-question-needs-controlled-outcomes = refl

record TerpeneDiscussionBoundary : Set where
  field
    historicalDispute      : CommentClaim
    genomicAssertion       : CommentClaim
    labelCritique          : CommentClaim
    correlationGuard       : CommentClaim
    steeringWheelAssertion : CommentClaim
    medicinalQuestion      : CommentClaim

canonicalDiscussionBoundary : TerpeneDiscussionBoundary
canonicalDiscussionBoundary = record
  { historicalDispute      = historical-taxonomy-claim
  ; genomicAssertion       = genomic-similarity-claim
  ; labelCritique          = label-predictiveness-critique
  ; correlationGuard       = correlation-warning
  ; steeringWheelAssertion = terpene-causality-denial
  ; medicinalQuestion      = medicinal-effect-question
  }
