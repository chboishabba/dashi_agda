module DASHI.Physics.Closure.CanonicalGaugeContractTheorem where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Algebra.GaugeGroupContract as GGC
open import DASHI.Physics.Constraints.ConcreteInstance as CI
open import DASHI.Physics.Closure.ParametricGaugeConstraintTheorem as PGCT

canonicalGaugeConstraintTheoremBase :
  PGCT.ParametricGaugeConstraintTheorem PGCT.canonicalConstraintGaugePackage
canonicalGaugeConstraintTheoremBase =
  PGCT.parametricGaugeConstraintTheorem PGCT.canonicalConstraintGaugePackage

canonicalGaugeEmergence : GGC.Emergence CI.C
canonicalGaugeEmergence =
  PGCT.ParametricGaugeConstraintTheorem.emergence
    canonicalGaugeConstraintTheoremBase

canonicalGaugeAdmissible : CI.C → Bool
canonicalGaugeAdmissible =
  PGCT.ParametricGaugeConstraintTheorem.admissibility
    canonicalGaugeConstraintTheoremBase

canonicalGaugeContractTheorem : GGC.UniquenessClaim CI.C
canonicalGaugeContractTheorem =
  PGCT.ParametricGaugeConstraintTheorem.uniqueness
    canonicalGaugeConstraintTheoremBase
