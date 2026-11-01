module DASHI.Core.DependencyPullbackCore where

open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Generic dependency/pullback surface.
--
-- A downstream claim cannot remain promoted after a dependency on which it
-- relies has been invalidated.  This is deliberately domain-neutral: sources,
-- replay artifacts, comparison laws, calibration receipts, and theorem
-- hypotheses can all be used as dependencies.
------------------------------------------------------------------------

data DependencyStatus : Set where
  live        : DependencyStatus
  invalidated : DependencyStatus

data PromotionStatus : Set where
  candidate  : PromotionStatus
  promoted   : PromotionStatus
  blocked    : PromotionStatus
  pulledBack : PromotionStatus

record DependencyEdge (Node : Set) : Set where
  constructor dependencyEdge
  field
    downstream : Node
    upstream   : Node

open DependencyEdge public

record PullbackWitness (Node : Set) : Set where
  constructor pullbackWitness
  field
    edge             : DependencyEdge Node
    upstreamStatus   : DependencyStatus
    downstreamBefore : PromotionStatus
    downstreamAfter  : PromotionStatus
    invalidationForcesPullback :
      upstreamStatus ≡ invalidated → downstreamAfter ≡ pulledBack

open PullbackWitness public

canonicalInvalidationPullback :
  {Node : Set} →
  DependencyEdge Node →
  PullbackWitness Node
canonicalInvalidationPullback edge =
  pullbackWitness edge invalidated promoted pulledBack (λ _ → refl)

pulledBackBlocksPromotion :
  {Node : Set} →
  (witness : PullbackWitness Node) →
  upstreamStatus witness ≡ invalidated →
  downstreamAfter witness ≡ pulledBack
pulledBackBlocksPromotion witness invalid =
  invalidationForcesPullback witness invalid
