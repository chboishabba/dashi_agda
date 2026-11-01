module DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicRegimePersistenceTheorem as PARP
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeInvarianceTheorem as PARI

record ParametricAlgebraicRegimeCoherenceTheorem
  (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  field
    regimePersistence :
      PARP.ParametricAlgebraicRegimePersistenceTheorem pkg
    regimeInvariance :
      PARI.ParametricAlgebraicRegimeInvarianceTheorem pkg
    coherentOnAdmissible :
      ∀ c →
      CCGP.admissible pkg c ≡ true →
      CCGP.admissible pkg c ≡ true

parametricAlgebraicRegimeCoherenceTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicRegimeCoherenceTheorem pkg
parametricAlgebraicRegimeCoherenceTheorem pkg =
  record
    { regimePersistence =
        PARP.parametricAlgebraicRegimePersistenceTheorem pkg
    ; regimeInvariance =
        PARI.parametricAlgebraicRegimeInvarianceTheorem pkg
    ; coherentOnAdmissible = λ c a → a
    }
