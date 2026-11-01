{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanUnifiedCorrelationClusteringLimitRound272Exact where

------------------------------------------------------------------------
-- ROUND272/R273 / CORRELATION TRAJECTORY -> SAME-LIMIT CLUSTERING
--
-- The B-facing input is now the least-privilege quantitative correlation
-- trajectory, not the full unified polymer norm.  Any valid producer may supply
-- it.  The UV/continuum lane supplies convergence of that same correlation
-- object; closedness of the common geometric upper bound then transports the
-- finite-scale inequality to the limit.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (_*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanRowCPostBC2PhysicalCompletionRound108Exact as R108
import DASHI.Physics.YangMills.BalabanUnifiedPolymerSchwingerNormExact as Unified

record SameCorrelationTrajectoryCompletion
    (trajectory : Unified.QuantitativeCorrelationDecayTrajectory) : Set₁ where
  field
    correlationLimit : Unified.Correlation trajectory

    CorrelationConverges :
      (Nat → Unified.Correlation trajectory) →
      Unified.Correlation trajectory → Set

    sameTrajectoryCorrelationConverges :
      CorrelationConverges
        (λ scale →
          Unified.correlationProjection trajectory
            (Unified.stateAtScale trajectory scale))
        correlationLimit

    -- Standard closed-order/evaluation consequence for the selected topology.
    uniformGeometricUpperClosedUnderLimit :
      ∀ left right →
      CorrelationConverges
        (λ scale →
          Unified.correlationProjection trajectory
            (Unified.stateAtScale trajectory scale))
        correlationLimit →
      (∀ scale →
        Unified.connectedCorrelationMagnitude trajectory
          (Unified.correlationProjection trajectory
            (Unified.stateAtScale trajectory scale)) left right
        ≤ Unified.amplitude trajectory
          * Power.rationalPower (Unified.ratio trajectory)
              (Unified.physicalDistance trajectory left right)) →
      Unified.connectedCorrelationMagnitude trajectory
        correlationLimit left right
      ≤ Unified.amplitude trajectory
        * Power.rationalPower (Unified.ratio trajectory)
            (Unified.physicalDistance trajectory left right)

open SameCorrelationTrajectoryCompletion public

limitCorrelationBound :
  (trajectory : Unified.QuantitativeCorrelationDecayTrajectory) →
  (completion : SameCorrelationTrajectoryCompletion trajectory) →
  ∀ left right →
  Unified.connectedCorrelationMagnitude trajectory
    (correlationLimit completion) left right
  ≤ Unified.amplitude trajectory
    * Power.rationalPower (Unified.ratio trajectory)
        (Unified.physicalDistance trajectory left right)
limitCorrelationBound trajectory completion left right =
  uniformGeometricUpperClosedUnderLimit completion left right
    (sameTrajectoryCorrelationConverges completion)
    (λ scale → Unified.geometricDecayAtEveryScale trajectory scale left right)

limitClustering :
  (trajectory : Unified.QuantitativeCorrelationDecayTrajectory) →
  SameCorrelationTrajectoryCompletion trajectory →
  R108.UniformGeometricConnectedClustering (Unified.Observable trajectory)
limitClustering trajectory completion = record
  { R108.UniformGeometricConnectedClustering.distance =
      Unified.physicalDistance trajectory
  ; R108.UniformGeometricConnectedClustering.connectedCovarianceMagnitude =
      Unified.connectedCorrelationMagnitude trajectory
        (correlationLimit completion)
  ; R108.UniformGeometricConnectedClustering.amplitude =
      Unified.amplitude trajectory
  ; R108.UniformGeometricConnectedClustering.ratio = Unified.ratio trajectory
  ; R108.UniformGeometricConnectedClustering.amplitudeNonnegative =
      Unified.amplitudeNonnegative trajectory
  ; R108.UniformGeometricConnectedClustering.ratioNonnegative =
      Unified.ratioNonnegative trajectory
  ; R108.UniformGeometricConnectedClustering.ratioStrictlyBelowOne =
      Unified.ratioStrictlyBelowOne trajectory
  ; R108.UniformGeometricConnectedClustering.connectedCovarianceBound =
      limitCorrelationBound trajectory completion
  }

round272UniformCorrelationBoundLimitCompilerLevel : ProofLevel
round272UniformCorrelationBoundLimitCompilerLevel = machineChecked

round272ClosedUpperBoundUnderCorrelationConvergenceLevel : ProofLevel
round272ClosedUpperBoundUnderCorrelationConvergenceLevel = standardImported

-- Reused UV/continuum content: same correlation projection converges to the
-- completed state.  It is not a second B-specific continuum construction.
round272SameCorrelationTrajectoryCompletionLevel : ProofLevel
round272SameCorrelationTrajectoryCompletionLevel = conditional

-- Canonical finite-scale B-facing theorem, independent of which tactic proves it.
round272PhysicalUniformCorrelationDecayLevel : ProofLevel
round272PhysicalUniformCorrelationDecayLevel =
  Unified.physicalYMCorrelationDecayTrajectoryLevel
