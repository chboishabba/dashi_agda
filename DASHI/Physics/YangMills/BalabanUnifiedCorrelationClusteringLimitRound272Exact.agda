{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanUnifiedCorrelationClusteringLimitRound272Exact where

------------------------------------------------------------------------
-- ROUND272 / SAME UNIFIED CORRELATION PROJECTION -> LIMIT CLUSTERING
--
-- R270 made physical uniform exponential clustering the canonical mass-gap
-- producer.  R271 made the unified polymer norm expose that quantitative bound
-- on its literal correlation projection.  The continuum lane already owns the
-- no-splicing theorem: once the unified RG state converges, its correlation
-- projection has the SAME completed-state limit.
--
-- Therefore cutoff/scale clustering does not require a new Yang--Mills theorem
-- at the limit.  The only additional ingredient is the standard topological
-- fact that a pointwise uniform closed upper bound survives convergence of the
-- correlation object.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanRowCPostBC2PhysicalCompletionRound108Exact as R108
import DASHI.Physics.YangMills.BalabanUnifiedPolymerSchwingerNormExact as Unified

record SameProducerCorrelationCompletion
    (producer : Unified.PhysicalYMUnifiedPolymerNormProducer) : Set₁ where
  field
    correlationLimit : Unified.WeightedCorrelation producer

    CorrelationConverges :
      (Nat → Unified.WeightedCorrelation producer) →
      Unified.WeightedCorrelation producer → Set

    sameProducerCorrelationConverges :
      CorrelationConverges
        (λ scale →
          Unified.correlationProjection (Unified.authority producer)
            (Unified.stateAtScale producer scale))
        correlationLimit

    -- Standard closed-order/evaluation consequence for the chosen correlation
    -- topology.  This is deliberately generic and source-independent.
    uniformGeometricUpperClosedUnderLimit :
      ∀ left right →
      CorrelationConverges
        (λ scale →
          Unified.correlationProjection (Unified.authority producer)
            (Unified.stateAtScale producer scale))
        correlationLimit →
      (∀ scale →
        Unified.connectedCorrelationMagnitude producer
          (Unified.correlationProjection (Unified.authority producer)
            (Unified.stateAtScale producer scale)) left right
        ≤ Unified.separationAmplitude producer
          * Power.rationalPower (Unified.separationRatio producer)
              (Unified.physicalDistance producer left right)) →
      Unified.connectedCorrelationMagnitude producer
        correlationLimit left right
      ≤ Unified.separationAmplitude producer
        * Power.rationalPower (Unified.separationRatio producer)
            (Unified.physicalDistance producer left right)

open SameProducerCorrelationCompletion public

limitCorrelationBound :
  (producer : Unified.PhysicalYMUnifiedPolymerNormProducer) →
  (completion : SameProducerCorrelationCompletion producer) →
  ∀ left right →
  Unified.connectedCorrelationMagnitude producer
    (correlationLimit completion) left right
  ≤ Unified.separationAmplitude producer
    * Power.rationalPower (Unified.separationRatio producer)
        (Unified.physicalDistance producer left right)
limitCorrelationBound producer completion left right =
  uniformGeometricUpperClosedUnderLimit completion left right
    (sameProducerCorrelationConverges completion)
    (λ scale → Unified.physicalSeparationDecay producer scale left right)

limitClustering :
  (producer : Unified.PhysicalYMUnifiedPolymerNormProducer) →
  SameProducerCorrelationCompletion producer →
  R108.UniformGeometricConnectedClustering
    (Unified.OrdinaryObservable producer)
limitClustering producer completion = record
  { R108.UniformGeometricConnectedClustering.distance =
      Unified.physicalDistance producer
  ; R108.UniformGeometricConnectedClustering.connectedCovarianceMagnitude =
      Unified.connectedCorrelationMagnitude producer
        (correlationLimit completion)
  ; R108.UniformGeometricConnectedClustering.amplitude =
      Unified.separationAmplitude producer
  ; R108.UniformGeometricConnectedClustering.ratio =
      Unified.separationRatio producer
  ; R108.UniformGeometricConnectedClustering.amplitudeNonnegative =
      Unified.separationAmplitudeNonnegative producer
  ; R108.UniformGeometricConnectedClustering.ratioNonnegative =
      Unified.separationRatioNonnegative producer
  ; R108.UniformGeometricConnectedClustering.ratioStrictlyBelowOne =
      Unified.separationRatioStrictlyBelowOne producer
  ; R108.UniformGeometricConnectedClustering.connectedCovarianceBound =
      limitCorrelationBound producer completion
  }

round272UniformCorrelationBoundLimitCompilerLevel : ProofLevel
round272UniformCorrelationBoundLimitCompilerLevel = machineChecked

-- Standard analysis/topology, not a new Yang--Mills estimate: evaluation and a
-- closed order cone preserve a common upper bound under the selected completed
-- correlation topology.
round272ClosedUpperBoundUnderCorrelationConvergenceLevel : ProofLevel
round272ClosedUpperBoundUnderCorrelationConvergenceLevel = standardImported

-- This is the already-existing same-unified-state continuum seam.  It belongs
-- to UV->continuum construction and must be reused by the mass-gap lane rather
-- than repaid there.
round272SameUnifiedCorrelationCompletionLevel : ProofLevel
round272SameUnifiedCorrelationCompletionLevel = conditional

-- After reuse of the continuum completion, the only genuinely YM-specific
-- quantitative mass-gap producer on this route is R271's physical separation
-- decay theorem on the same correlation projection.
round272PhysicalUniformCorrelationDecayLevel : ProofLevel
round272PhysicalUniformCorrelationDecayLevel =
  Unified.physicalYMUnifiedPolymerNormProducerLevel
