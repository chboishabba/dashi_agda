module DASHI.Physics.Closure.CanonicalGaugeConstraintBridgeTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Algebra.GaugeGroupContract as GGC
open import DASHI.Physics.Constraints.ConcreteInstance as CI
open import DASHI.Physics.Closure.CanonicalConstraintClosureTheorem as CCCT
open import DASHI.Physics.Closure.CanonicalGaugeContractTheorem as CGCT

record CanonicalGaugeConstraintBridgeTheorem : Setω where
  field
    closureTheorem : CCCT.CanonicalConstraintClosureTheorem
    gaugeContract : GGC.UniquenessClaim CI.C
    crAdmissible : GGC.UniquenessClaim.admissible gaugeContract CI.CR ≡ true
    cpAdmissible : GGC.UniquenessClaim.admissible gaugeContract CI.CP ≡ true
    ccAdmissible : GGC.UniquenessClaim.admissible gaugeContract CI.CC ≡ true
    crGauge≡SM :
      GGC.Emergence.pickGauge (GGC.UniquenessClaim.E gaugeContract) CI.CR
      ≡ GGC.SU3×SU2×U1
    cpGauge≡SM :
      GGC.Emergence.pickGauge (GGC.UniquenessClaim.E gaugeContract) CI.CP
      ≡ GGC.SU3×SU2×U1
    ccGauge≡SM :
      GGC.Emergence.pickGauge (GGC.UniquenessClaim.E gaugeContract) CI.CC
      ≡ GGC.SU3×SU2×U1

canonicalGaugeConstraintBridgeTheorem :
  CanonicalGaugeConstraintBridgeTheorem
canonicalGaugeConstraintBridgeTheorem =
  record
    { closureTheorem = CCCT.canonicalConstraintClosureTheorem
    ; gaugeContract = CGCT.canonicalGaugeContractTheorem
    ; crAdmissible = refl
    ; cpAdmissible = refl
    ; ccAdmissible = refl
    ; crGauge≡SM =
        GGC.UniquenessClaim.unique-SM
          CGCT.canonicalGaugeContractTheorem CI.CR refl
    ; cpGauge≡SM =
        GGC.UniquenessClaim.unique-SM
          CGCT.canonicalGaugeContractTheorem CI.CP refl
    ; ccGauge≡SM =
        GGC.UniquenessClaim.unique-SM
          CGCT.canonicalGaugeContractTheorem CI.CC refl
    }
