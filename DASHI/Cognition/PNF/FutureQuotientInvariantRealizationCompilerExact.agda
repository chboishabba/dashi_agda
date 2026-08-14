module DASHI.Cognition.PNF.FutureQuotientInvariantRealizationCompilerExact where

------------------------------------------------------------------------
-- FINITE FUTURE QUOTIENT -> INVARIANT DYNAMICAL REALIZATION COMPILER
--
-- The existing certified partition compiler computes a stable finite-depth
-- relation and proves that it is exactly canonical future equivalence.  Given a
-- concrete presentation/section of those classes, this module composes that
-- result with the canonical quotient-dynamics theorem.  The output therefore
-- contains both:
--
--   * a computed stable future partition with a finite rank bound; and
--   * the coarsest exact action system on the represented future classes.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.CertifiedFiniteFutureQuotientCompilerExact as Compiler
import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.GenericFuturePartitionRefinementExact as Refinement
import DASHI.Core.StablePartitionCanonicalFutureBridgeExact as Bridge
import DASHI.Cognition.PNF.CanonicalFutureMinimalDynamicalRealizationExact as Minimal

record PresentedFiniteFutureCompiler
    (State Action Observation : Set) : Set₁ where
  constructor presentedFiniteFutureCompiler
  field
    compiler : Compiler.CertifiedPartitionRefiner State Action Observation
    presentation : Future.FutureEquivalencePresentation
      (Bridge.deterministicSystem
        (Compiler.step compiler) (Compiler.actionLabel compiler))
      (Compiler.observe compiler)
    sectionedPresentation :
      Future.SectionedProjection (Future.classOf presentation)

open PresentedFiniteFutureCompiler public

record CompiledInvariantFutureRealization
    {State Action Observation : Set}
    (input : PresentedFiniteFutureCompiler State Action Observation) : Set₁ where
  constructor compiledInvariantFutureRealization
  field
    quotientCertificate : Compiler.CompiledFutureQuotient (compiler input)

    realization : Minimal.CanonicalFutureDynamicalRealization
      (Compiler.step (compiler input))
      (Compiler.actionLabel (compiler input))
      (Compiler.observe (compiler input))
      (presentation input)

    stableRelationIffPresentedClass :
      (left right : State) →
      Compiler.RelationIff
        (Refinement.RefinesToDepth
          (Compiler.stableDepth quotientCertificate)
          (Compiler.observe (compiler input))
          (Compiler.step (compiler input)) left right)
        (Future.classOf (presentation input) left
          ≡ Future.classOf (presentation input) right)

open CompiledInvariantFutureRealization public

compileInvariantFutureRealization :
  ∀ {State Action Observation}
    (input : PresentedFiniteFutureCompiler State Action Observation) →
  CompiledInvariantFutureRealization input
compileInvariantFutureRealization input =
  compiledInvariantFutureRealization
    quotient
    dynamics
    classBridge
  where
    quotient : Compiler.CompiledFutureQuotient (compiler input)
    quotient = Compiler.compileFutureQuotient (compiler input)

    dynamics : Minimal.CanonicalFutureDynamicalRealization
      (Compiler.step (compiler input))
      (Compiler.actionLabel (compiler input))
      (Compiler.observe (compiler input))
      (presentation input)
    dynamics = Minimal.compileCanonicalQuotientDynamics
      (presentation input) (sectionedPresentation input)

    classBridge : (left right : _) →
      Compiler.RelationIff
        (Refinement.RefinesToDepth
          (Compiler.stableDepth quotient)
          (Compiler.observe (compiler input))
          (Compiler.step (compiler input)) left right)
        (Future.classOf (presentation input) left
          ≡ Future.classOf (presentation input) right)
    classBridge left right = Compiler.relationIff
      (λ stableRelated →
        Future.classEqualityComplete (presentation input)
          (proj₁ (Compiler.canonicalExact quotient left right) stableRelated))
      (λ sameClass →
        proj₂ (Compiler.canonicalExact quotient left right)
          (Future.classEqualitySound (presentation input) sameClass))

compiledStableDepthIsBounded :
  ∀ {State Action Observation}
    {input : PresentedFiniteFutureCompiler State Action Observation} →
  Compiler.stableDepth (quotientCertificate (compileInvariantFutureRealization input))
  ≤ DASHI.Core.FiniteRankedRefinementStabilizationExact.rankBound
      (Compiler.process (compiler input))
compiledStableDepthIsBounded {input = input} =
  Compiler.depthBound
    (quotientCertificate (compileInvariantFutureRealization input))

------------------------------------------------------------------------
-- Boundary: the compiler now computes the canonical partition and its exact
-- quotient dynamics.  A further finite optimization may choose coordinates for
-- the quotient (bits, cyclotomic modes, Euclidean embeddings, etc.), but any
-- exact future-safe representation must factor onto this quotient and therefore
-- cannot legally erase one of its classes.
------------------------------------------------------------------------
