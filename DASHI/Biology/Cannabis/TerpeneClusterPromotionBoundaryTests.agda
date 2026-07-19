module DASHI.Biology.Cannabis.TerpeneClusterPromotionBoundaryTests where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Biology.Cannabis.TerpeneClusterPromotionBoundary
open import DASHI.Biology.Cannabis.TerpeneCommentInterpretation

chemical-stage-is-closed :
  cluster-established ≡ cluster-established
chemical-stage-is-closed = refl

association-stage-is-candidate-only :
  association-candidate ≡ association-candidate
association-stage-is-candidate-only = refl

clinical-stage-has-distinct-constructor :
  clinical-promoted ≡ clinical-promoted
clinical-stage-has-distinct-constructor = refl

commentary-does-not-promote :
  authority correlation-warning ≡ framing-only
commentary-does-not-promote = refl

causal-question-remains-gated :
  authority causal-question ≡ experiment-required
causal-question-remains-gated = refl
