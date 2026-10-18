module DASHI.Physics.Optics.DiffuserNoiseStableRecoveryExact where

-- A genuinely quantitative *conditional* inverse theorem:
-- When the selected optical code has a restricted lower Lipschitz bound,
-- and the measured exposure plus reconstruction residual are bounded,
-- the scene error is bounded by their sum.
--
-- This theorem does not assume sensor samples are independent, Gaussian,
-- unsaturated, or directly the same as wavefield amplitudes. Such claims
-- belong to a calibrated physical producer.

open import Agda.Primitive using (Set; Set₁)
open import Data.Nat using (ℕ; _≤_; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

record RestrictedInverseBudget (Scene Recorded : Set) : Set₁ where
  field
    admissible : Scene → Set
    encoder : Scene → Recorded
    sceneDistance : Scene → Scene → ℕ
    sampleDistance : Recorded → Recorded → ℕ
    conditionNumber : ℕ

    -- Restricted lower-bound *for this same calibrated encoder*.
    restrictedStability :
      (x y : Scene) →
      admissible x → admissible y →
      sceneDistance x y ≤
        conditionNumber * sampleDistance (encoder x) (encoder y)

    -- Triangle inequality for this same recorded-data metric.
    sampleTriangle :
      (a b c : Recorded) →
      sampleDistance a c ≤
        sampleDistance a b + sampleDistance b c

    -- Transport a sensor metric bound across scaling by conditionNumber.
    -- An instance on Nat distances may discharge this with monotonicity
    -- of multiplication; kept explicit to avoid selecting an arbitrary
    -- effective precision convention.
    scaleMonotone :
      (a b : ℕ) → a ≤ b →
      conditionNumber * a ≤ conditionNumber * b

    transitiveBound :
      (a b c : ℕ) → a ≤ b → b ≤ c → a ≤ c

open RestrictedInverseBudget public

record MeasuredReconstruction
    {Scene Recorded : Set}
    (M : RestrictedInverseBudget Scene Recorded)
    (actual estimate : Scene)
    (measurement : Recorded)
    (noise residual : ℕ) : Set where
  field
    actualAdmissible : admissible M actual
    estimateAdmissible : admissible M estimate

    measuredNoise :
      sampleDistance M (encoder M actual) measurement ≤ noise

    reconstructedResidual :
      sampleDistance M measurement (encoder M estimate) ≤ residual

    sumMonotone :
      ∀ {a b c d : ℕ} →
      a ≤ b → c ≤ d → a + c ≤ b + d

open MeasuredReconstruction public

-- "Multiple encodings regain information" is possible when the joint
-- recorded measurement retains separation. This theorem specifies the
-- *amount* of worst-case instability through conditionNumber.
stableReconstructionBound :
  ∀ {Scene Recorded : Set}
    (M : RestrictedInverseBudget Scene Recorded)
    (actual estimate : Scene)
    (measurement : Recorded)
    (noise residual : ℕ) →
  (R : MeasuredReconstruction M actual estimate
    measurement noise residual) →
  sceneDistance M actual estimate ≤
    conditionNumber M * (noise + residual)
stableReconstructionBound M actual estimate measurement noise residual R =
  transitiveBound M
    (sceneDistance M actual estimate)
    (conditionNumber M *
      sampleDistance M (encoder M actual) (encoder M estimate))
    (conditionNumber M * (noise + residual))
    (restrictedStability M actual estimate
      (actualAdmissible R) (estimateAdmissible R))
    (scaleMonotone M
      (sampleDistance M (encoder M actual) (encoder M estimate))
      (noise + residual)
      (transitiveBound M
        (sampleDistance M (encoder M actual) (encoder M estimate))
        (sampleDistance M (encoder M actual) measurement +
          sampleDistance M measurement (encoder M estimate))
        (noise + residual)
        (sampleTriangle M (encoder M actual)
          measurement (encoder M estimate))
        (sumMonotone R
          (measuredNoise R) (reconstructedResidual R))))

-- If the decoder fits no better than the actual scene, the residual can
-- be set equal to the noise budget, and the bound becomes 2*noise
-- (represented without relying on a particular arithmetic normal form).
stableWithMatchedResidual :
  ∀ {Scene Recorded : Set}
    (M : RestrictedInverseBudget Scene Recorded)
    (actual estimate : Scene) (measurement : Recorded) (error : ℕ) →
  (R : MeasuredReconstruction M actual estimate
    measurement error error) →
  sceneDistance M actual estimate ≤
    conditionNumber M * (error + error)
stableWithMatchedResidual M actual estimate measurement error R =
  stableReconstructionBound M actual estimate measurement error error R
