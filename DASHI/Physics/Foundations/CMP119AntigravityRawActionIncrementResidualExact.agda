{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityRawActionIncrementResidualExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; _+_; _-_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans; sym)

import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.Foundations.CMP119AntigravityCMP109WilsonDifferenceOrientationExact as UV

------------------------------------------------------------------------
-- SOURCE-NATIVE EDGE PROJECTOR WITH AN HONEST CORRECTION
--
-- The complete CMP119 action A_k is a NODE object and its Wilson
-- coefficient c_k is not itself the CMP109 step beta.  Instead compute
-- Pi(A_k-A_(k+1)) on T4's rational localized-action carrier and retain
-- the non-Wilson projector residual on each node.
--
-- When c_k=u_k the result is exactly
--
--   beta_(k+1) = Pi(A_k-A_(k+1)) - (r_k-r_(k+1)),
--
-- r_k = Pi(A_k)-c_k.
--
-- The correction vanishes if each node has only the specified Wilson
-- coefficient in the relevant projector, OR if the residual is invariant
-- across the step.  Neither physical property is assumed by the theorem.
------------------------------------------------------------------------

actionDifference : T4.LocalizedAction → T4.LocalizedAction → T4.LocalizedAction
actionDifference left right =
  T4.addLocalizedAction left (T4.scaleLocalizedAction (- 1ℚ) right)

projectorDifference :
  ∀ left right →
  T4.plaquetteCoefficientProjector (actionDifference left right)
  ≡ T4.plaquetteCoefficientProjector left
    - T4.plaquetteCoefficientProjector right
projectorDifference left right =
  trans (T4.plaquetteCoefficientAdditive
    left (T4.scaleLocalizedAction (- 1ℚ) right))
    (trans (cong
      (T4.plaquetteCoefficientProjector left +_)
      (T4.plaquetteCoefficientHomogeneous (- 1ℚ) right))
      (ℚRing.solve-∀
        (T4.plaquetteCoefficientProjector left)
        (T4.plaquetteCoefficientProjector right)))

module _
    {Density Background Fluctuation Wilson Small R Boundary Vacuum : Set}
    (source : Raw.CMP119SourceNativeRawState
      Density Background Fluctuation T4.LocalizedAction
      Wilson Small R Boundary Vacuum)
  where

  nodeProjector : Nat → ℚ
  nodeProjector k =
    T4.plaquetteCoefficientProjector (Raw.effectiveAction source k)

  nodeResidual : Nat → ℚ
  nodeResidual k = nodeProjector k - Raw.wilsonCoefficient source k

  projectedSourceEdge : Nat → ℚ
  projectedSourceEdge k =
    T4.plaquetteCoefficientProjector
      (actionDifference
        (Raw.effectiveAction source k)
        (Raw.effectiveAction source (suc k)))

  projectedEdgeSplitsWilsonAndResidual :
    ∀ k →
    projectedSourceEdge k
    ≡ (Raw.wilsonCoefficient source k
        - Raw.wilsonCoefficient source (suc k))
      + (nodeResidual k - nodeResidual (suc k))
  projectedEdgeSplitsWilsonAndResidual k =
    trans
      (projectorDifference
        (Raw.effectiveAction source k)
        (Raw.effectiveAction source (suc k)))
      (ℚRing.solve-∀
        (nodeProjector k)
        (nodeProjector (suc k))
        (Raw.wilsonCoefficient source k)
        (Raw.wilsonCoefficient source (suc k)))

  projectedEdgeAfterResidualCancellation :
    (∀ k → nodeResidual k ≡ nodeResidual (suc k)) →
    ∀ k →
    projectedSourceEdge k
    ≡ Raw.wilsonCoefficient source k
      - Raw.wilsonCoefficient source (suc k)
  projectedEdgeAfterResidualCancellation sameResidual k =
    trans
      (projectedEdgeSplitsWilsonAndResidual k)
      (trans
        (cong
          (λ r → (Raw.wilsonCoefficient source k
             - Raw.wilsonCoefficient source (suc k))
             + (r - nodeResidual (suc k)))
          (sameResidual k))
        (ℚRing.solve-∀
          (Raw.wilsonCoefficient source k)
          (Raw.wilsonCoefficient source (suc k))
          (nodeResidual (suc k))))

  selectedSourceBetaIsCorrectedProjectedEdge :
    (trajectory : Flow.SourceNormalizedCouplingTrajectory)
    (nodeMeaning : ∀ k →
      Raw.wilsonCoefficient source k
      ≡ Flow.inverseCoupling trajectory k) →
    ∀ k →
    Flow.beta trajectory (suc k)
    ≡ projectedSourceEdge k
      - (nodeResidual k - nodeResidual (suc k))
  selectedSourceBetaIsCorrectedProjectedEdge trajectory nodeMeaning k =
    trans
      (UV.sourceBetaIsWilsonCoefficientDifference
        trajectory (Raw.wilsonCoefficient source) nodeMeaning k)
      (trans
        (ℚRing.solve-∀
          (Raw.wilsonCoefficient source k)
          (Raw.wilsonCoefficient source (suc k))
          (nodeResidual k)
          (nodeResidual (suc k)))
        (cong
          (λ x → x - (nodeResidual k - nodeResidual (suc k)))
          (sym (projectedEdgeSplitsWilsonAndResidual k))))

------------------------------------------------------------------------
-- Finite RG telescope: net beta pays only the endpoint NON-WILSON drift.
-- This can be much tighter than summing the absolute value of every edge
-- correction, provided actual endpoint residual estimates can be proved.
------------------------------------------------------------------------

  selectedSourceBetaTelescopeByProjectedEndpoints :
    (trajectory : Flow.SourceNormalizedCouplingTrajectory)
    (nodeMeaning : ∀ k →
      Raw.wilsonCoefficient source k
      ≡ Flow.inverseCoupling trajectory k) →
    ∀ depth →
    Flow.betaPartial (Flow.beta trajectory) depth
    ≡ (nodeProjector zero - nodeProjector depth)
      - (nodeResidual zero - nodeResidual depth)
  selectedSourceBetaTelescopeByProjectedEndpoints
      trajectory nodeMeaning depth =
    trans
      (sym (Flow.inverseCouplingDifferenceIsBetaPartial trajectory depth))
      (trans
        (cong₂ _-_
          (sym (nodeMeaning zero))
          (sym (nodeMeaning depth)))
        (ℚRing.solve-∀
          (nodeProjector zero)
          (nodeProjector depth)
          (Raw.wilsonCoefficient source zero)
          (Raw.wilsonCoefficient source depth)))

------------------------------------------------------------------------
-- Opposite Wilson sign convention: c_k = -u_k. The projected action
-- difference changes sign, but the same non-Wilson edge drift survives.
------------------------------------------------------------------------

  selectedNegativeWilsonBetaIsCorrectedProjectedEdge :
    (trajectory : Flow.SourceNormalizedCouplingTrajectory)
    (nodeMeaning : ∀ k →
      Raw.wilsonCoefficient source k
      ≡ - Flow.inverseCoupling trajectory k) →
    ∀ k →
    Flow.beta trajectory (suc k)
    ≡ - projectedSourceEdge k
      + (nodeResidual k - nodeResidual (suc k))
  selectedNegativeWilsonBetaIsCorrectedProjectedEdge
      trajectory nodeMeaning k =
    trans
      (UV.sourceBetaIsNegativeWilsonCoefficientDifference
        trajectory (Raw.wilsonCoefficient source) nodeMeaning k)
      (trans
        (ℚRing.solve-∀
          (Raw.wilsonCoefficient source k)
          (Raw.wilsonCoefficient source (suc k))
          (nodeResidual k)
          (nodeResidual (suc k)))
        (cong
          (λ x → - x + (nodeResidual k - nodeResidual (suc k)))
          (sym (projectedEdgeSplitsWilsonAndResidual k))))
