module DASHI.Physics.Closure.CanonicalConstraintGaugePackage where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)

open import Agda.Builtin.Sigma using (Σ; _,_)
open import DASHI.Algebra.GaugeGroupContract as GGC

record CanonicalConstraintGaugePackage : Setω where
  field
    Carrier : Set
    _[_,]_ : Carrier → Carrier → Carrier
    closes :
      ∀ c₁ c₂ →
      Σ Carrier (λ c₃ → _[_,]_ c₁ c₂ ≡ c₃)
    admissible : Carrier → Bool
    admissibleClosed :
      ∀ c₁ c₂ →
      admissible c₁ ≡ true →
      admissible c₂ ≡ true →
      admissible (_[_,]_ c₁ c₂) ≡ true
    pickGauge : Carrier → GGC.Gauge
    uniqueGaugeOnAdmissible :
      ∀ c →
      admissible c ≡ true →
      pickGauge c ≡ GGC.SU3×SU2×U1

open CanonicalConstraintGaugePackage public
