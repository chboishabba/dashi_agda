module DASHI.Physics.Closure.ParametricAlgebraicConsistencyTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicClosureBundleTheorem as PACTB
open import DASHI.Physics.Closure.ParametricAlgebraicStabilityTheorem as PACTS
open import DASHI.Physics.Closure.ParametricGaugeConstraintBridgeTheorem as PGCBT

record ParametricAlgebraicConsistencyTheorem
  (P : CCGP.CanonicalConstraintGaugePackage) : Setω where
  field
    algebraicBundle : PACTB.ParametricAlgebraicClosureBundleTheorem P
    gaugeBridge : PGCBT.ParametricGaugeConstraintBridgeTheorem P
    stabilityConsistency :
      ∀ c →
      CCGP.admissible P c ≡ true →
      PACTS.ParametricAlgebraicStabilityTheorem.stableGaugeLeft
        (PACTB.ParametricAlgebraicClosureBundleTheorem.stability algebraicBundle)
        c
      ≡
      PACTS.ParametricAlgebraicStabilityTheorem.stableGaugeRight
        (PACTB.ParametricAlgebraicClosureBundleTheorem.stability algebraicBundle)
        c

parametricAlgebraicConsistencyTheorem :
  (P : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicConsistencyTheorem P
parametricAlgebraicConsistencyTheorem P =
  record
    { algebraicBundle = PACTB.parametricAlgebraicClosureBundleTheorem P
    ; gaugeBridge = PGCBT.parametricGaugeConstraintBridgeTheorem P
    ; stabilityConsistency = λ c a → refl
    }
