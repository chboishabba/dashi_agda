module DASHI.Physics.Closure.ParametricAlgebraicRegimeTransportConsistencyTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC
open import DASHI.Physics.Closure.ParametricAlgebraicTransportInvarianceTheorem as PATI

record ParametricAlgebraicRegimeTransportConsistencyTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicRegimeTransportConsistencyTheorem
  field
    regimeCoherence : PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    transportInvariance : PATI.ParametricAlgebraicTransportInvarianceTheorem pkg
    consistentOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicRegimeTransportConsistencyTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicRegimeTransportConsistencyTheorem pkg
buildParametricAlgebraicRegimeTransportConsistencyTheorem pkg =
  parametricAlgebraicRegimeTransportConsistencyTheorem
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (PATI.parametricAlgebraicTransportInvarianceTheorem pkg)
    (λ _ pf → pf)
