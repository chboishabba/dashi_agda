module DASHI.Physics.Closure.ParametricAlgebraicClosureTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)

open import Agda.Builtin.Sigma using (Σ)
open import DASHI.Algebra.GaugeGroupContract as GGC
open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricGaugeConstraintTheorem as PGCT
open import DASHI.Physics.Closure.ParametricGaugeConstraintBridgeTheorem as PGCBT

record ParametricAlgebraicClosureTheorem
  (P : CCGP.CanonicalConstraintGaugePackage) : Setω where
  field
    gaugeTheorem : PGCT.ParametricGaugeConstraintTheorem P
    bridgeTheorem : PGCBT.ParametricGaugeConstraintBridgeTheorem P
    carrierClosed :
      ∀ c₁ c₂ →
      Σ (CCGP.Carrier P) (λ c₃ → CCGP._[_,]_ P c₁ c₂ ≡ c₃)
    admissibilityClosed :
      ∀ c₁ c₂ →
      CCGP.admissible P c₁ ≡ true →
      CCGP.admissible P c₂ ≡ true →
      CCGP.admissible P (CCGP._[_,]_ P c₁ c₂) ≡ true
    gaugeStableOnAdmissible :
      ∀ c →
      CCGP.admissible P c ≡ true →
      GGC.Emergence.pickGauge
        (PGCT.ParametricGaugeConstraintTheorem.emergence gaugeTheorem) c
      ≡ GGC.SU3×SU2×U1

parametricAlgebraicClosureTheorem :
  (P : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicClosureTheorem P
parametricAlgebraicClosureTheorem P =
  record
    { gaugeTheorem = PGCT.parametricGaugeConstraintTheorem P
    ; bridgeTheorem = PGCBT.parametricGaugeConstraintBridgeTheorem P
    ; carrierClosed = CCGP.closes P
    ; admissibilityClosed = CCGP.admissibleClosed P
    ; gaugeStableOnAdmissible = CCGP.uniqueGaugeOnAdmissible P
    }
