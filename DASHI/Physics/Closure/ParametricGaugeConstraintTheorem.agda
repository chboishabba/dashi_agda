module DASHI.Physics.Closure.ParametricGaugeConstraintTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)

open import DASHI.Algebra.GaugeGroupContract as GGC
open import DASHI.Physics.Constraints.ConcreteInstance as CI
open import DASHI.Physics.Constraints.Bracket using (LieLike)
open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP

record ParametricGaugeConstraintTheorem
  (P : CCGP.CanonicalConstraintGaugePackage) : Setω where
  field
    emergence : GGC.Emergence (CCGP.Carrier P)
    admissibility :
      CCGP.Carrier P → Agda.Builtin.Bool.Bool
    uniqueness :
      GGC.UniquenessClaim (CCGP.Carrier P)
    closurePreservesAdmissibility :
      ∀ c₁ c₂ →
      admissibility c₁ ≡ true →
      admissibility c₂ ≡ true →
      admissibility (CCGP._[_,]_ P c₁ c₂) ≡ true

parametricGaugeConstraintTheorem :
  (P : CCGP.CanonicalConstraintGaugePackage) →
  ParametricGaugeConstraintTheorem P
parametricGaugeConstraintTheorem P =
  record
    { emergence =
        record { pickGauge = CCGP.pickGauge P }
    ; admissibility = CCGP.admissible P
    ; uniqueness =
        record
          { E = record { pickGauge = CCGP.pickGauge P }
          ; admissible = CCGP.admissible P
          ; unique-SM = CCGP.uniqueGaugeOnAdmissible P
          }
    ; closurePreservesAdmissibility = CCGP.admissibleClosed P
    }

canonicalConstraintGaugePackage : CCGP.CanonicalConstraintGaugePackage
canonicalConstraintGaugePackage =
  record
    { Carrier = CI.C
    ; _[_,]_ = LieLike._[_,]_ CI.L
    ; closes = λ c₁ c₂ → (LieLike._[_,]_ CI.L c₁ c₂ , refl)
    ; admissible = λ _ → true
    ; admissibleClosed = λ _ _ _ _ → refl
    ; pickGauge = λ _ → GGC.SU3×SU2×U1
    ; uniqueGaugeOnAdmissible = λ _ _ → refl
    }

canonicalParametricGaugeConstraintTheorem :
  ParametricGaugeConstraintTheorem canonicalConstraintGaugePackage
canonicalParametricGaugeConstraintTheorem =
  parametricGaugeConstraintTheorem canonicalConstraintGaugePackage
