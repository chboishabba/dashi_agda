module DASHI.Physics.Closure.ParametricAlgebraicRegimePersistenceTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeInvarianceTheorem as PARI
open import DASHI.Physics.Closure.ParametricAlgebraicPersistenceTheorem as PACTP

record ParametricAlgebraicRegimePersistenceTheorem
  (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  field
    regimeInvariant :
      ∀ c →
      CCGP.admissible pkg c ≡ true →
      CCGP.admissible pkg c ≡ true
    admissiblePersistent :
      ∀ c →
      CCGP.admissible pkg c ≡ true →
      CCGP.admissible pkg c ≡ true

parametricAlgebraicRegimePersistenceTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) ->
  ParametricAlgebraicRegimePersistenceTheorem pkg
parametricAlgebraicRegimePersistenceTheorem pkg =
  record
    { regimeInvariant =
        PARI.ParametricAlgebraicRegimeInvarianceTheorem.regimeInvariantOnAdmissible
          (PARI.parametricAlgebraicRegimeInvarianceTheorem pkg)
    ; admissiblePersistent =
        PACTP.ParametricAlgebraicPersistenceTheorem.persistenceOnAdmissible
          (PACTP.parametricAlgebraicPersistenceTheorem pkg)
    }
