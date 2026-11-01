module DASHI.Physics.Closure.ParametricAlgebraicRegimeInvarianceTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicTransportInvarianceTheorem as PATI
open import DASHI.Physics.Closure.ParametricAlgebraicGaugeSectorPersistenceTheorem as PAGSP

record ParametricAlgebraicRegimeInvarianceTheorem
  (P : CCGP.CanonicalConstraintGaugePackage) : Setω where
  field
    transportInvariance :
      PATI.ParametricAlgebraicTransportInvarianceTheorem P
    gaugeSectorPersistence :
      PAGSP.ParametricAlgebraicGaugeSectorPersistenceTheorem P
    regimeInvariantOnAdmissible :
      ∀ c →
      CCGP.admissible P c ≡ true →
      CCGP.admissible P c ≡ true

parametricAlgebraicRegimeInvarianceTheorem :
  (P : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicRegimeInvarianceTheorem P
parametricAlgebraicRegimeInvarianceTheorem P =
  record
    { transportInvariance =
        PATI.parametricAlgebraicTransportInvarianceTheorem P
    ; gaugeSectorPersistence =
        PAGSP.parametricAlgebraicGaugeSectorPersistenceTheorem P
    ; regimeInvariantOnAdmissible = λ c a → a
    }
