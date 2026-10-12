module DASHI.Physics.Plasma.Phase243ConsumerKernelCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerKernelQuotientPresentationExact as Kernel
import DASHI.Physics.Plasma.Phase243OrbitQuotientExact as Q54
import DASHI.Physics.Plasma.Phase243ConsumerDescentExact as Descent

------------------------------------------------------------------------
-- CORE54 VERSUS THE CANONICAL CONSUMER KERNEL
--
-- Once a declared consumer is phase invariant, Core54 is a sufficient sectioned
-- observer.  The repository's canonical consumer-kernel theorem therefore says
-- Core54 factors ONTO the canonical quotient determined by equality of that
-- consumer's outputs.
--
-- This is deliberately one-way: Core54 need not be minimal for every consumer.
-- Multiple Core54 classes may still have identical B-spread, curvature, orbit,
-- Pareto or other declared consumer outcomes.  Any additional compression must
-- be indexed by that consumer rather than promoted to a universal phase quotient.
------------------------------------------------------------------------

core54FactorsCanonicalConsumerKernel :
  ∀ {Outcome : Set} →
  (c : Descent.PhaseInvariantConsumer Outcome) →
  Kernel.FactorizationThroughConsumerKernel
    (Descent.consumer c)
    Q54.quotientCore
    (Kernel.canonicalConsumerKernelPresentation (Descent.consumer c))
core54FactorsCanonicalConsumerKernel c =
  Kernel.sectionedSufficientObserverFactorsCanonical
    Descent.core54SectionedProjection
    (Descent.consumer c)
    (Descent.phaseInvariantConsumerIsCore54Sufficient c)

record Phase243ConsumerKernelBoundary : Set where
  constructor phase243-consumer-kernel-boundary
  field
    core54SufficientObserverFactorsCanonicalKernel : Bool
    core54SufficientObserverFactorsCanonicalKernelIsTrue :
      core54SufficientObserverFactorsCanonicalKernel ≡ true
    core54IsLeastForEveryConsumer : Bool
    core54IsLeastForEveryConsumerIsFalse :
      core54IsLeastForEveryConsumer ≡ false
    furtherCompressionMustBeConsumerIndexed : Bool
    furtherCompressionMustBeConsumerIndexedIsTrue :
      furtherCompressionMustBeConsumerIndexed ≡ true

canonicalPhase243ConsumerKernelBoundary : Phase243ConsumerKernelBoundary
canonicalPhase243ConsumerKernelBoundary =
  phase243-consumer-kernel-boundary true refl false refl true refl
