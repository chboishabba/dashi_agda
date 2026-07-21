module DASHI.Physics.Closure.NSPeriodicFourierCancellationAlgebra where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

------------------------------------------------------------------------
-- Exact algebra behind the far-low commutator.
--
-- For p + q = k and p · u(p) = 0, one has
--
--   u(p) · q = u(p) · (k - p) = u(p) · k.
--
-- This module proves that statement from the additive/dot-product laws only.
-- No norm estimate, multiplier regularity or sampled certificate is used here.
------------------------------------------------------------------------

record FourierCancellationAlgebra (i : Level) : Set (lsuc i) where
  field
    Mode Vector Scalar : Set i

    zero : Scalar
    modeSubtract : Mode → Mode → Mode
    scalarSubtract : Scalar → Scalar → Scalar
    dot : Vector → Mode → Scalar

    dotSubtract : ∀ u k p →
      dot u (modeSubtract k p) ≡
      scalarSubtract (dot u k) (dot u p)

    subtractZeroRight : ∀ a →
      scalarSubtract a zero ≡ a

open FourierCancellationAlgebra public

record DivergenceFreeTriad
    {i : Level}
    (A : FourierCancellationAlgebra i) : Set (lsuc i) where
  field
    lowMode highMode outputMode : Mode A
    lowVelocity : Vector A

    resonance :
      highMode ≡ modeSubtract A outputMode lowMode

    lowModeDivergenceFree :
      dot A lowVelocity lowMode ≡ zero A

open DivergenceFreeTriad public

divergenceFreeFourierCancellation :
  ∀ {i} {A : FourierCancellationAlgebra i} →
  (T : DivergenceFreeTriad A) →
  dot A (lowVelocity T) (highMode T) ≡
  dot A (lowVelocity T) (outputMode T)
divergenceFreeFourierCancellation {A = A} T =
  trans
    (cong (dot A (lowVelocity T)) (resonance T))
    (trans
      (dotSubtract A
        (lowVelocity T)
        (outputMode T)
        (lowMode T))
      (trans
        (cong
          (λ value →
            scalarSubtract A
              (dot A (lowVelocity T) (outputMode T))
              value)
          (lowModeDivergenceFree T))
        (subtractZeroRight A
          (dot A (lowVelocity T) (outputMode T)))))

-- Audit alias matching the periodic Fourier notation.
lowHighDerivativeMovesToOutputFrequency :
  ∀ {i} {A : FourierCancellationAlgebra i} →
  (T : DivergenceFreeTriad A) →
  dot A (lowVelocity T) (highMode T) ≡
  dot A (lowVelocity T) (outputMode T)
lowHighDerivativeMovesToOutputFrequency =
  divergenceFreeFourierCancellation
