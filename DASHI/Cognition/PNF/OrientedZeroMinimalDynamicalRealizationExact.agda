module DASHI.Cognition.PNF.OrientedZeroMinimalDynamicalRealizationExact where

------------------------------------------------------------------------
-- ORIENTED-ZERO REGRESSION FOR THE MINIMAL DYNAMICAL REALIZATION COMPILER
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.CanonicalFutureMinimalDynamicalRealizationExact as Minimal
import DASHI.Cognition.PNF.FutureQuotientInvariantRealizationCompilerExact as Compile
import DASHI.Cognition.PNF.OrientedZeroCanonicalFutureExact as Canonical
import DASHI.Cognition.PNF.OrientedZeroCanonicalPartitionPresentationExact as Partition
import DASHI.Cognition.PNF.OrientedZeroCertifiedCompilerExact as Certified
import DASHI.Cognition.PNF.OrientedZeroFutureQuotientExact as Wave
import DASHI.Core.CertifiedFiniteFutureQuotientCompilerExact as CoreCompiler
import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.GenericFuturePartitionRefinementExact as Refinement
import DASHI.Core.StablePartitionCanonicalFutureBridgeExact as Bridge

waveFuturePresentation : Future.FutureEquivalencePresentation
  (Bridge.deterministicSystem Partition.step Partition.label) Wave.scalar
waveFuturePresentation = Future.futureEquivalencePresentation
  Wave.Wave4
  (λ state → state)
  sound
  complete
  where
    sound : ∀ {left right} → left ≡ right →
      Future.FutureObservationEquivalent
        (Bridge.deterministicSystem Partition.step Partition.label)
        Wave.scalar left right
    sound refl = Future.futureEquivalentRefl _

    complete : ∀ {left right} →
      Future.FutureObservationEquivalent
        (Bridge.deterministicSystem Partition.step Partition.label)
        Wave.scalar left right →
      left ≡ right
    complete {left} {right} equivalent =
      Partition.depthOneRefinementInjective
        (proj₂ (Partition.depthOneExactlyCanonicalFuture left right) equivalent)

wavePresentationSection :
  Future.SectionedProjection (Future.classOf waveFuturePresentation)
wavePresentationSection = Future.sectionedProjection
  (λ state → state)
  (λ state → refl)

waveCanonicalDynamics : Minimal.CanonicalFutureDynamicalRealization
  Partition.step Partition.label Wave.scalar waveFuturePresentation
waveCanonicalDynamics = Minimal.compileCanonicalQuotientDynamics
  waveFuturePresentation wavePresentationSection

waveQuotientStepIsFineStep :
  (action : Canonical.Action) (state : Wave.Wave4) →
  Minimal.quotientStep waveCanonicalDynamics action state
  ≡ Partition.step action state
waveQuotientStepIsFineStep action state = refl

presentedWaveCompiler :
  Compile.PresentedFiniteFutureCompiler
    Wave.Wave4 Canonical.Action Wave.Scalar3
presentedWaveCompiler = Compile.presentedFiniteFutureCompiler
  Certified.orientedZeroCompiler
  waveFuturePresentation
  wavePresentationSection

compiledWaveInvariantRealization :
  Compile.CompiledInvariantFutureRealization presentedWaveCompiler
compiledWaveInvariantRealization =
  Compile.compileInvariantFutureRealization presentedWaveCompiler

compiledWaveStillFindsDepthOne :
  CoreCompiler.stableDepth
    (Compile.quotientCertificate compiledWaveInvariantRealization) ≡ 1
compiledWaveStillFindsDepthOne = refl

compiledStableRelationIsExactWaveEquality :
  (left right : Wave.Wave4) →
  Refinement.RefinesToDepth 1 Wave.scalar Partition.step left right →
  left ≡ right
compiledStableRelationIsExactWaveEquality left right =
  Partition.depthOneRefinementInjective

------------------------------------------------------------------------
-- The regression realizes:
--   3-state present observation
--     -> computed depth-one four-class future quotient
--     -> exact four-state quotient dynamics.
-- No future-safe representation can legally merge -0 and +0.
------------------------------------------------------------------------
