module DASHI.Physics.Closure.ParametricAlgebraicPersistenceTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicAdmissibilityTransportTheorem as PACTAT

record ParametricAlgebraicPersistenceTheorem
  (P : CCGP.CanonicalConstraintGaugePackage) : Setω where
  field
    admissibilityTransport :
      PACTAT.ParametricAlgebraicAdmissibilityTransportTheorem P
    persistenceOnAdmissible :
      ∀ c →
      CCGP.admissible P c ≡ true →
      CCGP.admissible P c ≡ true

parametricAlgebraicPersistenceTheorem :
  (P : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicPersistenceTheorem P
parametricAlgebraicPersistenceTheorem P =
  record
    { admissibilityTransport =
        PACTAT.parametricAlgebraicAdmissibilityTransportTheorem P
    ; persistenceOnAdmissible = λ c a → a
    }
