module DASHI.Physics.Closure.ParametricGaugeConstraintBridgeTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Algebra.GaugeGroupContract as GGC
open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricGaugeConstraintTheorem as PGCT

record ParametricGaugeConstraintBridgeTheorem
  (P : CCGP.CanonicalConstraintGaugePackage) : Setω where
  field
    gaugeTheorem : PGCT.ParametricGaugeConstraintTheorem P
    gaugeContract : GGC.UniquenessClaim (CCGP.Carrier P)
    admissibleClosedOnCarrier :
      ∀ c₁ c₂ →
      GGC.UniquenessClaim.admissible gaugeContract c₁ ≡ true →
      GGC.UniquenessClaim.admissible gaugeContract c₂ ≡ true →
      GGC.UniquenessClaim.admissible gaugeContract
        (CCGP._[_,]_ P c₁ c₂) ≡ true
    gaugeUniqueOnAdmissibleCarrier :
      ∀ c →
      GGC.UniquenessClaim.admissible gaugeContract c ≡ true →
      GGC.Emergence.pickGauge (GGC.UniquenessClaim.E gaugeContract) c
        ≡ GGC.SU3×SU2×U1

parametricGaugeConstraintBridgeTheorem :
  (P : CCGP.CanonicalConstraintGaugePackage) →
  ParametricGaugeConstraintBridgeTheorem P
parametricGaugeConstraintBridgeTheorem P =
  record
    { gaugeTheorem = PGCT.parametricGaugeConstraintTheorem P
    ; gaugeContract =
        PGCT.ParametricGaugeConstraintTheorem.uniqueness
          (PGCT.parametricGaugeConstraintTheorem P)
    ; admissibleClosedOnCarrier =
        PGCT.ParametricGaugeConstraintTheorem.closurePreservesAdmissibility
          (PGCT.parametricGaugeConstraintTheorem P)
    ; gaugeUniqueOnAdmissibleCarrier = CCGP.uniqueGaugeOnAdmissible P
    }
