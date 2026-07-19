module DASHI.Biology.Cannabis.TerpeneCommentInterpretation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Biology.Cannabis.TerpeneClusterPromotionBoundary

-- The comments raise useful objections, but they occupy different evidential
-- roles.  This module records those roles without promoting the comments
-- themselves into biological or clinical facts.
data CommentRole : Set where
  label-critique
  correlation-warning
  causal-question
  unsupported-overstatement : CommentRole

data ClaimAuthority : Set where
  framing-only
  observational-candidate
  experiment-required
  blocked : ClaimAuthority

authority : CommentRole → ClaimAuthority
authority label-critique             = framing-only
authority correlation-warning        = framing-only
authority causal-question            = experiment-required
authority unsupported-overstatement  = blocked

label-comment-is-not-genomic-proof :
  authority label-critique ≡ framing-only
label-comment-is-not-genomic-proof = refl

correlation-comment-is-a-guard :
  authority correlation-warning ≡ framing-only
correlation-comment-is-a-guard = refl

clinical-question-needs-experiment :
  authority causal-question ≡ experiment-required
clinical-question-needs-experiment = refl

-- The strongest scientifically useful synthesis of the post and comments.
record TerpeneDiscussionBoundary : Set where
  field
    paperSurface            : CommentRole
    labelDispute            : CommentRole
    associationDispute      : CommentRole
    medicinalEffectQuestion : CommentRole

canonicalDiscussionBoundary : TerpeneDiscussionBoundary
canonicalDiscussionBoundary = record
  { paperSurface            = label-critique
  ; labelDispute            = label-critique
  ; associationDispute      = correlation-warning
  ; medicinalEffectQuestion = causal-question
  }
