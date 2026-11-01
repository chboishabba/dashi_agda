module DASHI.Physics.Closure.ParametricAlgebraicAdmissibilityTransportTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicConsistencyTheorem as PACTX

record ParametricAlgebraicAdmissibilityTransportTheorem
  (P : CCGP.CanonicalConstraintGaugePackage) : Setω where
  field
    algebraicConsistency : PACTX.ParametricAlgebraicConsistencyTheorem P
    admissibilityTransport :
      ∀ c →
      CCGP.admissible P c ≡ true →
      CCGP.admissible P c ≡ true

parametricAlgebraicAdmissibilityTransportTheorem :
  (P : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicAdmissibilityTransportTheorem P
parametricAlgebraicAdmissibilityTransportTheorem P =
  record
    { algebraicConsistency = PACTX.parametricAlgebraicConsistencyTheorem P
    ; admissibilityTransport = λ c a → a
    }
