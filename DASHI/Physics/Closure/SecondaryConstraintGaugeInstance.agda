module DASHI.Physics.Closure.SecondaryConstraintGaugeInstance where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Maybe.Base using (Maybe; just; nothing)

open import DASHI.Algebra.GaugeGroupContract as GGC
open import DASHI.Physics.Constraints.Bracket using (LieLike)
open import DASHI.Physics.Constraints.ConcreteInstance as CI
open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricGaugeConstraintTheorem as PGCT

SecondaryCarrier : Set
SecondaryCarrier = Maybe CI.C

combine : SecondaryCarrier → SecondaryCarrier → SecondaryCarrier
combine (just c₁) (just c₂) = just (LieLike._[_,]_ CI.L c₁ c₂)
combine _ _ = nothing

secondaryAdmissible : SecondaryCarrier → Bool
secondaryAdmissible (just _) = true
secondaryAdmissible nothing = false

secondaryPickGauge : SecondaryCarrier → GGC.Gauge
secondaryPickGauge (just _) = GGC.SU3×SU2×U1
secondaryPickGauge nothing = GGC.Other

secondaryConstraintGaugePackage : CCGP.CanonicalConstraintGaugePackage
secondaryConstraintGaugePackage =
  record
    { Carrier = SecondaryCarrier
    ; _[_,]_ = combine
    ; closes = λ c₁ c₂ → (combine c₁ c₂ , refl)
    ; admissible = secondaryAdmissible
    ; admissibleClosed = λ where
        (just _) (just _) refl refl → refl
    ; pickGauge = secondaryPickGauge
    ; uniqueGaugeOnAdmissible = λ where
        (just _) refl → refl
    }

secondaryParametricGaugeConstraintTheorem :
  PGCT.ParametricGaugeConstraintTheorem secondaryConstraintGaugePackage
secondaryParametricGaugeConstraintTheorem =
  PGCT.parametricGaugeConstraintTheorem secondaryConstraintGaugePackage
