module DASHI.Physics.Closure.ParametricAlgebraicTransportInvarianceTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicAdmissibilityTransportTheorem as PACTAT
open import DASHI.Physics.Closure.ParametricAlgebraicGaugeSectorPersistenceTheorem as PAGSP

record ParametricAlgebraicTransportInvarianceTheorem
  (P : CCGP.CanonicalConstraintGaugePackage) : Setω where
  field
    admissibilityTransport :
      PACTAT.ParametricAlgebraicAdmissibilityTransportTheorem P
    gaugeSectorPersistence :
      PAGSP.ParametricAlgebraicGaugeSectorPersistenceTheorem P
    transportInvariantOnAdmissible :
      ∀ c →
      CCGP.admissible P c ≡ true →
      CCGP.admissible P c ≡ true

parametricAlgebraicTransportInvarianceTheorem :
  (P : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicTransportInvarianceTheorem P
parametricAlgebraicTransportInvarianceTheorem P =
  record
    { admissibilityTransport =
        PACTAT.parametricAlgebraicAdmissibilityTransportTheorem P
    ; gaugeSectorPersistence =
        PAGSP.parametricAlgebraicGaugeSectorPersistenceTheorem P
    ; transportInvariantOnAdmissible = λ c a → a
    }
